/-
  * Common.FileSim — union-of-resolutions glue for file-copying binaries.

  TRUST BOUNDARY: shared proof library, not the trusted specification.
  Image-INDEPENDENT.
(v_addi pc 4) ...`;
  - file offsets/counts are `word`s bridged with `word_to_nat`; the
    read-effect return value is `len_word bs` and offsets advance by
    `bv` addition (`off + len_word bs`, the Specs spelling).
  A binary whose only observables are its exit code and the FINAL FILE
  SYSTEM (no channel I/O at all: openat/close and file read/write emit
  no trace events) has as behavior a UNION over syscall resolutions of
  (exit code, final fs) outcomes.  This file provides:
  - `to_fout segs ms model U`: from machine state `ms` and model
    `model`, the reachable set of (code, fs) outcomes is EXACTLY `U`.
    Leaves are exit ecalls; interior nodes are event-free,
    never-halting, never-erroring syscalls branching over every
    admissible resolution (`tfo_sys`).
  - the trace characterization (`fout_obs_iff`): `obs_trace` is
    exactly the prefixes of `[ExitEv code fs]` for the outcomes in `U`;
    plus no-error (`fout_no_error_run`) and the `Equivalence.equiv`-level
    glue (`fout_strong_equiv`).
  - per-syscall decoding through the verified checker for the
    file-system surface: openat (O_RDONLY hit/miss and
    O_WRONLY|O_CREAT|O_TRUNC), file read, file write, close — as
    ergonomic `to_fout` nodes.
  - `read_cstr` bridges (path strings out of argv stack memory),
    fs/fd-table algebra, and `file_read`/`file_write` arithmetic for
    the copy-loop bookkeeping.
  - may-error reachability helpers (`msteps_spec_err_error`,
    `reaches_error_star`) plus the stronger universal-error helper
    `msteps_spec_err_all_traces_error` for deterministic Unmodeled paths.
  NOTES.
  - `Z` → `Int`; `Z_to_bv n z` → `BitVec.ofInt n z`; `bv_unsigned w` →
    `(w.toNat : Int)`; `bv_and` → `&&&`; `firstn`/`skipn` →
    `List.take`/`List.drop`; `length` → `List.length`; `lia` → `omega`.
  - `Section WithFP1`'s `Context {fx : FPState}` becomes the ambient
    `variable [fx : FPState]` of the same name, exactly as `PropExec`,
    `CatExec` and `AllocSim` do; the section's `fp_regs`/`fp_csr` are
    `fx.fp_regs`/`fx.fp_csr`.
  - `Section WithSegs`'s `Variable segs : list Segment` becomes an
    EXPLICIT leading parameter of every declaration that mentions it,
    as `ExitSim`/`WallSim`/`StreamSim` do for their sections.  The nested
    `Section OpenNodes` carries the same variable and gets the same
    treatment; `End OpenNodes`/`End WithFP1` add nothing.
  - `mkEntry sp brk0 mb rnd` is the `ExecEntry` constructor
    `⟨sp, brk0, mb, rnd⟩`.
 Their `Hh`/`Hlazy`
    are the `with_fds`/`with_fs` projections, which are `rfl` (`with_fds`/
    `with_fs` leave `m_halted`/`m_vm_lazy` alone).
  - `mkCfg ms model` is the `config` constructor `⟨ms, model⟩`;
    `mkEffect r ws zs` is `mkEffect r ws zs`; `mkst regs pc mem rom` is
    `mkst regs pc mem rom`; `SNext`/`SError` are `.SNext`/`.SError`.
  - `syscall_spec … Unmodeled` / `… (Ok eff model' evs)` are
    `.unmodeled` / `.ok eff model' evs`; `destruct` on an `Outcome` is
    `cases`, on a `machine_result` likewise.
-/
import LinuxSem.Common.WallSim
import LinuxSem.Common.StreamSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StreamExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.ErrEscape
import LinuxSem.Common.SimInv
import LinuxSem.Checks.ExecutableSpecs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.FileSim

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
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Fs.Open
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
open LinuxSem.Common.ErrEscape

variable [fx : FPState]

/- =========================================================================
   Model plumbing
   ========================================================================= -/

theorem with_fds_fs (f : List (word × FdEntry)) (m : Model) : m_fs (with_fds f m) = m_fs m :=
  rfl

theorem with_fds_halted (f : List (word × FdEntry)) (m : Model) :
    m_halted (with_fds f m) = m_halted m :=
  rfl

theorem with_fds_fds (f : List (word × FdEntry)) (m : Model) : m_fds (with_fds f m) = f :=
  rfl

theorem with_fs_fs (f : Fs.Fs) (m : Model) : m_fs (with_fs f m) = f :=
  rfl

theorem with_fs_halted (f : Fs.Fs) (m : Model) : m_halted (with_fs f m) = m_halted m :=
  rfl

theorem with_fs_fds (f : Fs.Fs) (m : Model) : m_fds (with_fs f m) = m_fds m :=
  rfl

/- The argument-register index lemmas `arg_reg_0/1/2` live in
    `Common.PropExec` (imported above), so they are shared across the
    Common sim/exec files and every FileSim-based example. -/

/-- `set_reg` at the literal a0 index . -/
theorem set_reg_10 (st : machine_state) (r : word) :
    set_reg st 10 r = { st with ms_regs := regupd st.ms_regs 10 r } := by
  simp only [set_reg, regupd]
  rw [show bv_eqb (10 : reg) 0 = false from by decide]
  simp

/-- advance-past-svc of a ret-only effect at the raw ecall record. -/
theorem adv_eff_ret (regs : BvMap word) (pc : word) (x8 : word)
    (mem rom : word → Option byte) (r : word) :
    advance_past_svc
      (apply_effect
        { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
          ms_svc_pending := some x8, ms_resv := none, ms_fcsr := fx.fp_csr,
          ms_mem := mem, ms_rom := rom } (mkEffect r [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom := by
  simp only [advance_past_svc, apply_effect, mkEffect, apply_writes, apply_copies,
    apply_zeros, apply_unmaps, set_reg_10, ms_pc, mkst, regupd, b_npc4]

/-- Copy-in provenance does not change the machine-state transition. -/
theorem adv_eff_ret_copyins (regs : BvMap word) (pc : word) (x8 : word)
    (mem rom : word → Option byte) (r : word) (copyins : List (word × Nat)) :
    advance_past_svc
      (apply_effect
        { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
          ms_svc_pending := some x8, ms_resv := none, ms_fcsr := fx.fp_csr,
          ms_mem := mem, ms_rom := rom }
        (with_copyins copyins (mkEffect r [] [])))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom :=
  adv_eff_ret regs pc x8 mem rom r

/- =========================================================================
   sys_input projections
   ========================================================================= -/

theorem in_sysno_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 :=
  rfl

theorem in_arg0_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 :=
  rfl

theorem in_arg1_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 :=
  rfl

theorem in_arg2_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 :=
  rfl

theorem in_mem_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_mem = ms_read_byte ms :=
  rfl

theorem in_wmem_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_wmem = ms_writable_byte segs ms :=
  rfl

/- =========================================================================
   fs algebra (fs_set / fs_lookup)
   ========================================================================= -/

theorem path_eqb_neq (p q : path) (h : p ≠ q) : path_eqb p q = false := by
  cases hb : path_eqb p q with
  | false => rfl
  | true => exact absurd ((path_eqb_eq p q).mp hb) h

theorem fs_lookup_set_eq (fs : Fs) (p : path) (d : List byte) :
    fs_lookup (fs_set fs p d) p = some d := by
  induction fs with
  | nil => simp [fs_set, fs_lookup, path_eqb_refl]
  | cons qd r ih =>
    obtain ⟨q, dq⟩ := qd
    simp only [fs_set]
    by_cases h1 : path_ltb p q = true
    · rw [ite_eq_left h1]
      simp [fs_lookup, path_eqb_refl]
    · rw [ite_eq_right h1]
      by_cases h2 : path_eqb p q = true
      · rw [ite_eq_left h2]
        simp [fs_lookup, path_eqb_refl]
      · rw [ite_eq_right h2]
        simpa only [fs_lookup, ite_eq_right h2] using ih

theorem fs_lookup_set_neq (fs : Fs) (p : path) (d : List byte) (q : path)
    (hne : q ≠ p) : fs_lookup (fs_set fs p d) q = fs_lookup fs q := by
  induction fs with
  | nil => simp [fs_set, fs_lookup, path_eqb_neq q p hne]
  | cons rd r ih =>
    obtain ⟨r, dr⟩ := rd
    simp only [fs_set]
    by_cases h1 : path_ltb p r = true
    · rw [ite_eq_left h1]
      simp [fs_lookup, path_eqb_neq q p hne]
    · rw [ite_eq_right h1]
      by_cases h2 : path_eqb p r = true
      · rw [ite_eq_left h2]
        have hpr : p = r := (path_eqb_eq p r).mp h2
        subst hpr
        simp [fs_lookup, path_eqb_neq q p hne]
      · rw [ite_eq_right h2]
        simp only [fs_lookup]
        by_cases h3 : path_eqb q r = true
        · rw [ite_eq_left h3, ite_eq_left h3]
        · rw [ite_eq_right h3, ite_eq_right h3]
          exact ih

theorem path_ltb_irrefl (p : path) : path_ltb p p = false := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [path_ltb]
    unfold bv_ltu
    rw [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · simp
    · simp [path_eqb_refl, ih]

theorem fs_set_set (fs : Fs) (p : path) (d d' : List byte) :
    fs_set (fs_set fs p d) p d' = fs_set fs p d' := by
  induction fs with
  | nil => simp [fs_set, path_ltb_irrefl, path_eqb_refl]
  | cons qd r ih =>
    obtain ⟨q, dq⟩ := qd
    simp only [fs_set]
    by_cases h1 : path_ltb p q = true
    · rw [ite_eq_left h1]
      simp [fs_set, path_ltb_irrefl, path_eqb_refl, h1]
    · rw [ite_eq_right h1]
      by_cases h2 : path_eqb p q = true
      · rw [ite_eq_left h2]
        have hpq : p = q := (path_eqb_eq p q).mp h2
        subst hpq
        simp [fs_set, path_ltb_irrefl, path_eqb_refl]
      · rw [ite_eq_right h2]
        simp [fs_set, h1, h2, ih]

/- =========================================================================
   fd-table algebra
   ========================================================================= -/

/- This tree's `fd_lookup`/`fd_insert`/`fd_remove` spell their key test
   `k == fd` (`BEq`), which is `bv_eqb` by definition (`Riscv.Prelude`).
   These three bridges keep the `bv_eqb` lemmas applicable. -/
theorem beq_refl {n : Nat} (a : BitVec n) : (a == a) = true := by
  simp [bv_eqb]

theorem beq_false {n : Nat} (a b : BitVec n) (h : a ≠ b) : (a == b) = false := by
  simpa [bv_eqb] using PropExec.bv_eqb_neq a b h

/-- The same two bridges at `bv_eqb`, the spelling `read_cstr_aux` and the
    syscall specs use. -/
theorem bv_eqb_true {n : Nat} (a : BitVec n) : bv_eqb a a = true :=
  PropExec.bv_eqb_refl a

theorem bv_eqb_false {n : Nat} (a b : BitVec n) (h : a ≠ b) : bv_eqb a b = false :=
  PropExec.bv_eqb_neq a b h

theorem beq_eq {n : Nat} (a b : BitVec n) (h : (a == b) = true) : a = b :=
  (bv_eqb_eq a b).mp (by simpa [bv_eqb] using h)

--This tree states these two after `fd_lookup_filter_neq`; here
-- they are hoisted above it, which is the only order that lets the filter
-- step in that proof be a rewrite.
theorem filter_fd_cons_keep {B : Type} (fds : List (word × B)) (k : word) (e : B)
    (fd : word) (hne : k ≠ fd) :
    List.filter (fun p => !(p.1 == fd)) ((k, e) :: fds)
      = (k, e) :: List.filter (fun p => !(p.1 == fd)) fds := by
  simp only [List.filter]
  rw [beq_false k fd hne]
  simp only [Bool.not_false, ite_eq_left rfl]

theorem filter_fd_cons_drop {B : Type} (fds : List (word × B)) (fd : word) (e : B) :
    List.filter (fun p => !(p.1 == fd)) ((fd, e) :: fds)
      = List.filter (fun p => !(p.1 == fd)) fds := by
  simp only [List.filter]
  rw [beq_refl]
  simp only [Bool.not_true, ite_eq_left rfl]

theorem fd_lookup_cons_eq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) :
    fd_lookup ((fd, e) :: fds) fd = some e := by
  simp [fd_lookup, beq_refl]

theorem fd_lookup_cons_neq (fds : List (word × FdEntry)) (k : word) (e : FdEntry)
    (fd : word) (hne : k ≠ fd) :
    fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd := by
  simp [fd_lookup, beq_false k fd hne]

theorem fd_lookup_cons_None (fds : List (word × FdEntry)) (k : word) (e : FdEntry)
    (fd : word) (h : fd_lookup ((k, e) :: fds) fd = none) :
    k ≠ fd ∧ fd_lookup fds fd = none := by
  simp only [fd_lookup] at h
  by_cases hk : (k == fd) = true
  · rw [hk] at h
    simp at h
  · have hkf : (k == fd) = false := by simpa using hk
    rw [hkf] at h
    exact ⟨fun hc => by rw [hc, beq_refl] at hkf; simp at hkf, h⟩

theorem fd_filter_id (fds : List (word × FdEntry)) (fd : word)
    (h : fd_lookup fds fd = none) :
    List.filter (fun p => !(p.1 == fd)) fds = fds := by
  induction fds with
  | nil => rfl
  | cons ke r ih =>
    obtain ⟨k, e⟩ := ke
    obtain ⟨hne, h'⟩ := fd_lookup_cons_None r k e fd h
    simp only [List.filter]
    rw [beq_false k fd hne]
    simp only [Bool.not_false]
    rw [ih h']

theorem fd_insert_fresh (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (h : fd_lookup fds fd = none) : fd_insert fds fd e = (fd, e) :: fds := by
  unfold fd_insert
  rw [fd_filter_id fds fd h]

theorem fd_lookup_filter_neq (fds : List (word × FdEntry)) (fd fd' : word)
    (hne : fd' ≠ fd) :
    fd_lookup (List.filter (fun p => !(p.1 == fd)) fds) fd' = fd_lookup fds fd' := by
  induction fds with
  | nil => rfl
  | cons ke r ih =>
    obtain ⟨k, e⟩ := ke
    by_cases hk : k = fd
    · rw [hk] at *
      rw [filter_fd_cons_drop, ih]
      simp only [fd_lookup]
      rw [beq_false fd fd' (Ne.symm hne)]
      simp
    · rw [filter_fd_cons_keep _ _ _ _ hk]
      simp only [fd_lookup, ih]

theorem fd_lookup_insert_eq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) :
    fd_lookup (fd_insert fds fd e) fd = some e := by
  unfold fd_insert
  exact fd_lookup_cons_eq _ _ _

theorem fd_lookup_insert_neq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (fd' : word) (hne : fd' ≠ fd) :
    fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd' := by
  unfold fd_insert
  rw [fd_lookup_cons_neq _ _ _ _ (Ne.symm hne)]
  exact fd_lookup_filter_neq fds fd fd' hne

theorem fd_lookup_remove_neq (fds : List (word × FdEntry)) (fd fd' : word)
    (hne : fd' ≠ fd) :
    fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd' := by
  unfold fd_remove
  exact fd_lookup_filter_neq fds fd fd' hne

theorem fd_lookup_some_none_neq (fds : List (word × FdEntry)) (a b : word)
    (ea : FdEntry) (ha : fd_lookup fds a = some ea) (hb : fd_lookup fds b = none) :
    a ≠ b := by
  rintro rfl
  rw [ha] at hb
  simp at hb

/-- A concrete free fd after one open over the three standard channels
    (stdin/stdout/stderr already occupied). -/
theorem free_fd_after_open (x y z : FdEntry) (fdin : word) (e : FdEntry) :
    ∃ w, fd_lookup
        (fd_insert
          [(BitVec.ofInt 64 0, x), (BitVec.ofInt 64 1, y), (BitVec.ofInt 64 2, z)]
          fdin e) w = none
      ∧ (w.toNat : Int) < 2 ^ 31 := by
  by_cases h : fdin = BitVec.ofInt 64 3
  · subst h
    refine ⟨BitVec.ofInt 64 4, ?_, ?_⟩
    · rw [fd_lookup_insert_neq _ _ _ _ (by decide)]
      simp [fd_lookup, beq_refl]
    · decide
  · refine ⟨BitVec.ofInt 64 3, ?_, ?_⟩
    · rw [fd_lookup_insert_neq _ _ _ _ (Ne.symm h)]
      simp [fd_lookup, beq_refl]
    · decide

/- =========================================================================
   file_read / file_write arithmetic
   ========================================================================= -/

theorem length_file_read (data : List byte) (off count : word) :
    (file_read data off count).length
      = min (word_to_nat count) (data.length - word_to_nat off) := by
  rw [file_read_unguarded, List.length_take, List.length_drop]

theorem file_read_nil (data : List byte) (off count : word)
    (h : data.length ≤ word_to_nat off) : file_read data off count = [] := by
  rw [file_read_unguarded, List.drop_eq_nil_of_le h, List.take_nil]

/-- Appending write: writing at exactly the end of the file. -/
theorem file_write_append (data : List byte) (off : word) (bs : List byte)
    (hoff : word_to_nat off = data.length) : file_write data off bs = data ++ bs := by
  cases bs with
  | nil => simp [file_write]
  | cons b bs =>
    simp only [file_write]
    rw [hoff, Nat.sub_self, List.replicate_zero, List.append_nil]
    have htake : List.take data.length data = data := List.take_length ..
    rw [htake]
    have hdrop : List.drop (data.length + (b :: bs).length) data = [] :=
      List.drop_eq_nil_of_le (by simp)
    rw [hdrop, List.append_nil]

theorem firstn_add {A : Type} (l : List A) (n m : Nat) :
    List.take (n + m) l = List.take n l ++ List.take m (List.drop n l) :=
  List.take_add ..

/-- One copy step: current content `List.take (word_to_nat off) data`
    extended by the chunk just read at `off`.  The fd offset is a `word`,
    and the equation is hypothesis-free. -/
theorem copy_step (data : List byte) (off count : word) :
    List.take (word_to_nat off) data ++ file_read data off count
      = List.take (word_to_nat off
          + min (word_to_nat count) (data.length - word_to_nat off)) data := by
  rw [file_read_unguarded, firstn_add]
  congr 1
  have hd : (List.drop (word_to_nat off) data).length
      = data.length - word_to_nat off := List.length_drop ..
  by_cases h : word_to_nat count ≤ data.length - word_to_nat off
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega)]
    rw [← hd, List.take_length]
    rw [List.take_of_length_le (by omega)]

/- =========================================================================
   read_cstr bridges (through the rdn merged view)
   ========================================================================= -/

/-- The merged read view `rdn` chains over — equal to `ms_read_byte` of a
    state whose rom is `seg_rom segs`. -/
def mrb (segs : List Segment) (mem : word → Option byte) : word → Option byte :=
  fun a =>
    match mem a with
    | some b => some b
    | none => seg_rom segs a

theorem ms_read_byte_mrb (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) :
    ms_read_byte (mkst regs pc mem (seg_rom segs)) = mrb segs mem :=
  rfl

theorem ms_read_byte_rec_mrb (segs : List Segment) (regs : BvMap word)
    (fr : BvMap word) (pc : word) (sv : Option word) (rv : Option word)
    (fc : BitVec 32) (mem : word → Option byte) :
    ms_read_byte
      { ms_regs := regs, ms_fregs := fr, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := rv, ms_fcsr := fc, ms_mem := mem, ms_rom := seg_rom segs }
      = mrb segs mem :=
  rfl

/-- The first byte read by `rdn` is exactly the `mrb` value at `a`. -/
theorem mrb_first (segs : List Segment) (mem : word → Option byte) (a : word)
    (n : Nat) (b : byte) (rest : List byte)
    (H : rdn segs mem a (n + 1) = some (b :: rest)) : mrb segs mem a = some b := by
  simp only [rdn, mrb] at H
  cases h1 : mem a <;> cases h2 : seg_rom segs a <;>
    cases h3 : rdn segs mem (a + 1) n <;> simp_all [mrb]

/-- The remaining bytes read by `rdn`. -/
theorem rdn_tail (segs : List Segment) (mem : word → Option byte) (a : word)
    (n : Nat) (b : byte) (rest : List byte)
    (H : rdn segs mem a (n + 1) = some (b :: rest)) :
    rdn segs mem (a + 1) n = some rest := by
  simp only [rdn, mrb] at H
  cases h1 : mem a <;> cases h2 : seg_rom segs a <;>
    cases h3 : rdn segs mem (a + 1) n <;> simp_all [mrb]

theorem read_cstr_aux_of_rdn (segs : List Segment) (str : List byte) (fuel : Nat)
    (mem : word → Option byte) (a : word)
    (Hf : str.length < fuel) (Hnz : (BitVec.ofInt 8 0) ∉ str)
    (Hr : rdn segs mem a (str.length + 1) = some (str ++ [BitVec.ofInt 8 0])) :
    read_cstr_aux (mrb segs mem) a fuel = .CstrOk str := by
  induction str generalizing fuel mem a with
  | nil =>
    cases fuel with
    | zero => simp at Hf
    | succ fuel =>
      have Hb0 : mrb segs mem a = some (BitVec.ofInt 8 0) :=
        mrb_first segs mem a 0 _ _ (by simpa using Hr)
      simp [read_cstr_aux, Hb0, bv_eqb_true]
  | cons b str ih =>
    cases fuel with
    | zero => simp at Hf
    | succ fuel =>
      have Hb : b ≠ BitVec.ofInt 8 0 := by
        rintro rfl
        exact Hnz (List.mem_cons_self ..)
      have Hfirst : mrb segs mem a = some b :=
        mrb_first segs mem a (str.length + 1) b _ (by simpa using Hr)
      have Htail : rdn segs mem (a + 1) (str.length + 1)
          = some (str ++ [BitVec.ofInt 8 0]) :=
        rdn_tail segs mem a (str.length + 1) b _ (by simpa using Hr)
      have Hlen : str.length < fuel := by simpa using Hf
      have Hnz' : (BitVec.ofInt 8 0) ∉ str := by
        intro h
        exact Hnz (List.mem_cons_of_mem b h)
      simp only [read_cstr_aux, Hfirst]
      rw [bv_eqb_false b (BitVec.ofInt 8 0) Hb]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih fuel mem (a + 1) Hlen Hnz' Htail]

theorem read_cstr_of_rdn (segs : List Segment) (mem : word → Option byte) (a : word)
    (str : List byte) (Hlen : str.length ≤ 4095)
    (Hnz : (BitVec.ofInt 8 0) ∉ str)
    (Hr : rdn segs mem a (str.length + 1) = some (str ++ [BitVec.ofInt 8 0])) :
    read_cstr (mrb segs mem) a = .CstrOk str := by
  unfold read_cstr
  have hpm : path_max = 4096 := rfl
  rw [hpm]
  exact read_cstr_aux_of_rdn segs str 4096 mem a (by omega) Hnz Hr

/-- `fuel` readable non-NUL bytes: the scan runs out of bound, which is
    `CstrTooLong` — the -ENAMETOOLONG case, NOT a fault. -/
theorem read_cstr_aux_toolong_of_rdn (segs : List Segment) (fuel : Nat)
    (bs : List byte) (mem : word → Option byte) (a : word)
    (Hlen : bs.length = fuel) (Hnz : (BitVec.ofInt 8 0) ∉ bs)
    (Hr : rdn segs mem a fuel = some bs) :
    read_cstr_aux (mrb segs mem) a fuel = .CstrTooLong := by
  induction fuel generalizing bs mem a with
  | zero =>
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero Hlen
    subst hbs
    rfl
  | succ fuel ih =>
    cases bs with
    | nil => simp at Hlen
    | cons b bs =>
      have Hlen' : bs.length = fuel := by simpa using Hlen
      have Hb : b ≠ BitVec.ofInt 8 0 := by
        rintro rfl
        exact Hnz (List.mem_cons_self ..)
      have Hfirst : mrb segs mem a = some b :=
        mrb_first segs mem a fuel b bs (by simpa using Hr)
      have Htail : rdn segs mem (a + 1) fuel = some bs :=
        rdn_tail segs mem a fuel b bs (by simpa using Hr)
      have Hnz' : (BitVec.ofInt 8 0) ∉ bs := by
        intro h
        exact Hnz (List.mem_cons_of_mem b h)
      simp only [read_cstr_aux, Hfirst]
      rw [bv_eqb_false b (BitVec.ofInt 8 0) Hb]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih bs mem (a + 1) Hlen' Hnz' Htail]

theorem read_cstr_toolong_of_rdn (segs : List Segment) (mem : word → Option byte)
    (a : word) (bs : List byte) (Hlen : bs.length = 4096)
    (Hnz : (BitVec.ofInt 8 0) ∉ bs) (Hr : rdn segs mem a 4096 = some bs) :
    read_cstr (mrb segs mem) a = .CstrTooLong := by
  unfold read_cstr
  have hpm : path_max = 4096 := rfl
  rw [hpm]
  exact read_cstr_aux_toolong_of_rdn segs 4096 bs mem a Hlen Hnz Hr

/- =========================================================================
   argv strings as NUL-terminated byte runs and prefixes
   ========================================================================= -/

theorem read_argv_cstr_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (Hk : k < av.length)
    (Hnw : (sp.toNat : Int)
      + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k) ((av[k]?.getD []).length + 1)
      = some (av[k]?.getD [] ++ [BitVec.ofInt 8 0]) := by
  obtain ⟨pre, post, E, Hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd Hk
  have H := read_at_offset_image segs ph sp av ev uid hw rnd pre
    (av[k]?.getD [] ++ [BitVec.ofInt 8 0]) post ((av[k]?.getD []).length + 1) E
    (by rw [List.length_append, List.length_cons, List.length_nil]) Hnw
  rw [Hlen] at H
  simp only [cat_argv_ptr_offset sp av ev k Hk, cat_string_base, nat_to_word_add_merge]
  exact H

theorem read_argv_prefix_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k n : Nat) (uid hw : word) (rnd : EntryDraw)
    (Hk : k < av.length) (Hn : n ≤ (av[k]?.getD []).length)
    (Hnw : (sp.toNat : Int)
      + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k) n
      = some (List.take n (av[k]?.getD [])) := by
  obtain ⟨pre, post, E, Hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd Hk
  have H := read_at_offset_image segs ph sp av ev uid hw rnd pre
    (List.take n (av[k]?.getD []))
    ((List.drop n (av[k]?.getD []) ++ [BitVec.ofInt 8 0]) ++ post) n ?_ ?_ Hnw
  · rw [Hlen] at H
    simp only [cat_argv_ptr_offset sp av ev k Hk, cat_string_base, nat_to_word_add_merge]
    exact H
  · rw [E]
    simp only [List.append_assoc]
    rw [← List.append_assoc (List.take n (av[k]?.getD []))
      (List.drop n (av[k]?.getD [])) ([BitVec.ofInt 8 0] ++ post), List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left Hn]

/- =========================================================================
   to_fout: the exact (exit code, final fs) outcome set
   ========================================================================= -/

def fout_trace (o : word × Fs.Fs) : List event := [event.ExitEv o.1 o.2]

/-- `to_fout`: the reachable (exit code, final fs) outcome set is exactly
    `U`.  Leaves are exit ecalls; interior nodes are event-free,
    never-halting, never-erroring syscalls branching over every admissible
    resolution. -/
inductive to_fout (segs : List Segment) : machine_state → Model →
    ((word × Fs.Fs) → Prop) → Prop where
  | exit (ms : machine_state) (model : Model) (x8 : word)
      (U : (word × Fs.Fs) → Prop)
      (hsvc : ms.ms_svc_pending = some x8)
      (hx8 : is_exit_no x8)
      (hU : ∀ o, U o ↔ o = (ms_gpr ms 0 &&& BitVec.ofInt 64 255, m_fs model)) :
      to_fout segs ms model U
  | step (ms ms' : machine_state) (model : Model) (U : (word × Fs.Fs) → Prop)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hto : to_fout segs ms' model U) :
      to_fout segs ms model U
  | sys (ms : machine_state) (model : Model) (x8 : word)
      (T : SyscallEffect → Model → (word × Fs.Fs) → Prop)
      (U : (word × Fs.Fs) → Prop)
      (hsvc : ms.ms_svc_pending = some x8)
      (hne : ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled)
      (hrec : ∃ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
      (hshape : ∀ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
        evs = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = [])
      (hcont : ∀ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
        to_fout segs (advance_past_svc (apply_effect ms eff)) model' (T eff model'))
      (hU : ∀ o, U o ↔ (∃ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)
          ∧ T eff model' o)) :
      to_fout segs ms model U

/-- Prepend a deterministic instruction run. -/
theorem tfo_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (H : msteps segs ms ms')
    (Ht : to_fout segs ms' model U) : to_fout segs ms model U := by
  induction H with
  | mst_refl ms => exact Ht
  | mst_step ms ms' ms'' hsvc hstep hm ih =>
    exact to_fout.step ms ms' model U hsvc hstep (ih Ht)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tfo_equiv (segs : List Segment) (ms : machine_state) (model : Model)
    (U V : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U)
    (HV : ∀ o, V o ↔ U o) : to_fout segs ms model V := by
  revert V
  induction Hto with
  | exit ms model x8 U hsvc hx8 hU =>
    intro V HV
    exact to_fout.exit ms model x8 V hsvc hx8 (fun o => (HV o).trans (hU o))
  | step ms ms' model U hsvc hstep hto ih =>
    intro V HV
    exact to_fout.step ms ms' model V hsvc hstep (ih V HV)
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro V HV
    exact to_fout.sys ms model x8 T V hsvc hne hrec hshape hcont
      (fun o => (HV o).trans (hU o))

/-- Every `to_fout` outcome set is inhabited. -/
theorem to_fout_nonempty (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U) : ∃ o, U o := by
  induction Hto with
  | exit ms model x8 U hsvc hx8 hU => exact ⟨_, (hU _).mpr rfl⟩
  | step ms ms' model U hsvc hstep hto ih => exact ih
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    obtain ⟨eff, model', evs, hspec⟩ := hrec
    obtain ⟨o, ho⟩ := ih eff model' evs hspec
    exact ⟨o, (hU o).mpr ⟨eff, model', evs, hspec, ho⟩⟩

/-- One-step inversion at a `tfo_sys` ecall. -/
theorem sstep_fsys_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hne : ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled)
    (Hshape : ∀ eff model' evs',
      Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs') →
      evs' = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = [])
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    ∃ eff model', Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' []) ∧
      evs = [] ∧ st = .SNext ⟨advance_past_svc (apply_effect ms eff), model'⟩ := by
  cases Hss with
  | instr ms model ms' model' hh hsvc hstep =>
    rw [Hsvc] at hsvc
    simp at hsvc
  | instr_fault ms model hh hsvc hstep =>
    rw [Hsvc] at hsvc
    simp at hsvc
  | instr_unmodeled ms model hh hsvc hstep =>
    rw [Hsvc] at hsvc
    simp at hsvc
  | syscall ms model x8' eff model' model'' evs hh hsvc hspec hh' hmat =>
    have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
    rw [hx8] at hspec
    obtain ⟨hevs, -, hlazy⟩ := Hshape eff model' evs hspec
    have hmat' : materialize_model_accesses model' (syscall_effect_accesses eff) = some model' :=
      materialize_model_accesses_no_lazy model' _ hlazy
    rw [hmat'] at hmat
    obtain rfl := Option.some.inj hmat
    rw [hevs] at hspec
    exact ⟨eff, model', hspec, hevs, rfl⟩
  | syscall_materialization_fault ms model x8' eff model' evs hh hsvc hspec hh' hmat =>
    exfalso
    have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
    rw [hx8] at hspec
    obtain ⟨-, -, hlazy⟩ := Hshape eff model' evs hspec
    rw [materialize_model_accesses_no_lazy model' _ hlazy] at hmat
    simp at hmat
  | exit ms model x8' eff model' evs code hh hsvc hspec hh' hk =>
    exfalso
    have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
    rw [hx8] at hspec
    obtain ⟨-, hm, -⟩ := Hshape eff model' evs hspec
    rw [hm] at hh'
    simp at hh'
  | killed ms model x8' eff model' evs sig hh hsvc hspec hk =>
    exfalso
    have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
    rw [hx8] at hspec
    obtain ⟨-, hm, -⟩ := Hshape eff model' evs hspec
    rw [m_killed_of_m_halted_none model' hm] at hk
    simp at hk
  | syscall_unmodeled ms model x8' hh hsvc hspec =>
    exfalso
    have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
    rw [hx8] at hspec
    exact Hne hspec

/- -------------------------------------------------------------------------
   Trace characterization.
   ------------------------------------------------------------------------- -/

/-- The omni reading of a file-copying run: every execution halts with
    one of the outcomes, having emitted exactly its exit event.  One
    induction over `to_fout`; at a syscall node the successors are
    exactly the admissible resolutions (`sstep_fsys_inv`), each covered
    by the induction hypothesis at its post-model. -/
def fout_post (U : (word × Fs.Fs) → Prop) : post :=
  fun tr o => ∃ out, U out ∧ tr = fout_trace out ∧ exits_with out.1 tr o

theorem to_fout_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U) :
    m_halted model = none → m_vm_lazy model = [] →
    OmniRun.exec segs ⟨ms, model⟩ (fout_post U) := by
  induction Hto with
  | exit ms model x8 U hsvc hx8 hU =>
    intro Hh Hlazy
    refine exec_step_only segs ⟨ms, model⟩ (fout_post U)
      [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
      ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ ?_ ?_ ?_
    · exact sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms 0 &&& BitVec.ofInt 64 255) Hh hsvc
        (exit_dispatch_ok (sys_input segs ms x8) model (by rw [in_sysno_si]; exact hx8))
        rfl rfl
    · intro evs st hss
      exact sstep_exit_inv segs ms model x8 evs st Hh hsvc hx8 hss
    · refine exec_halted segs
        ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ _ ?_ ?_
      · simp [m_halted_with_halted]
      · refine ⟨(ms_gpr ms 0 &&& BitVec.ofInt 64 255, m_fs model), (hU _).mpr rfl, ?_, ?_, ?_⟩
        · simp [fout_trace]
        · simp [exits_with, m_halted_with_halted]
        · simp [m_killed_with_halted]
  | step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy
    refine exec_step_only segs ⟨ms, model⟩ (fout_post U) [] ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hss
    · simpa using ih Hh Hlazy
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro Hh Hlazy
    refine exec.step ⟨ms, model⟩ (fout_post U) Hh ?_ ?_ ?_
    · obtain ⟨eff, model', evs, hspec⟩ := hrec
      obtain ⟨hevs, hh', hlazy'⟩ := hshape eff model' evs hspec
      exact ⟨evs, .SNext ⟨advance_past_svc (apply_effect ms eff), model'⟩,
        sstep.syscall ms model x8 eff model' model' evs Hh hsvc hspec hh'
          (by rw [materialize_model_accesses_no_lazy model' _ hlazy'])⟩
    · intro evs hss
      obtain ⟨eff, model', hspec, hevs, hst⟩ :=
        sstep_fsys_inv segs ms model x8 evs .SError Hh Hlazy hsvc hne hshape hss
      cases hst
    · intro evs c' hss
      obtain ⟨eff, model', hspec, hevs, hst⟩ :=
        sstep_fsys_inv segs ms model x8 evs (.SNext c') Hh Hlazy hsvc hne hshape hss
      cases hst
      obtain ⟨-, hh', hlazy'⟩ := hshape eff model' [] hspec
      rw [hevs]
      refine exec_conseq segs _ (fout_post (T eff model')) (fout_post U)
        (ih eff model' [] hspec hh' hlazy') ?_
      intro tr o H
      obtain ⟨out, Hout, Heq, Hx⟩ := H
      exact ⟨out, (hU out).mpr ⟨eff, model', [], hspec, Hout⟩, by simpa using Heq, Hx⟩

theorem to_fout_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (tr : List event) (c : config) (Hstar : star segs ⟨ms, model⟩ tr c) :
    ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  obtain ⟨tr', o, -, hQ⟩ :=
    exec_realizes segs c (fun tr' o => fout_post U (tr ++ tr') o)
      (exec_star segs ⟨ms, model⟩ (fout_post U) tr c
        (to_fout_exec segs ms model U Hto Hh Hlazy) Hstar)
  obtain ⟨out, Hout, Heq, -⟩ := hQ
  exact ⟨out, Hout, by rw [← Heq]; exact is_prefix_app tr tr'⟩

theorem to_fout_star_admits (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U) :
    m_halted model = none → m_vm_lazy model = [] →
    ∀ o, U o → ∃ c, star segs ⟨ms, model⟩ (fout_trace o) c := by
  induction Hto with
  | exit ms model x8 U hsvc hx8 hU =>
    intro Hh Hlazy o Ho
    have ho := (hU o).mp Ho
    subst ho
    refine ⟨⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩, star_one segs _ _ _ ?_⟩
    exact sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
      (ms_gpr ms 0 &&& BitVec.ofInt 64 255) Hh hsvc
      (exit_dispatch_ok (sys_input segs ms x8) model (by rw [in_sysno_si]; exact hx8)) rfl rfl
  | step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy o Ho
    obtain ⟨c, Hstar⟩ := ih Hh Hlazy o Ho
    exact ⟨c, star.step ⟨ms, model⟩ [] ⟨ms', model⟩ (fout_trace o) c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])) Hstar⟩
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro Hh Hlazy o Ho
    obtain ⟨eff, model', evs, hspec, Ht⟩ := (hU o).mp Ho
    obtain ⟨hevs, hh', hlazy'⟩ := hshape eff model' evs hspec
    rw [hevs] at hspec
    obtain ⟨c, Hstar⟩ := ih eff model' [] hspec hh' hlazy' o Ht
    exact ⟨c, star.step ⟨ms, model⟩ [] ⟨advance_past_svc (apply_effect ms eff), model'⟩
      (fout_trace o) c
      (sstep.syscall ms model x8 eff model' model' [] Hh hsvc hspec hh'
        (by rw [materialize_model_accesses_no_lazy model' _ hlazy'])) Hstar⟩

theorem to_fout_progress (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U) :
    m_halted model = none → m_vm_lazy model = [] →
    ∀ (evs : List event) (st : step_to), sstep segs ⟨ms, model⟩ evs st →
    ∃ ms' model', st = .SNext ⟨ms', model'⟩ ∧
      (m_halted model' ≠ none ∨
       (m_halted model' = none ∧ m_vm_lazy model' = [] ∧
        ∃ U', to_fout segs ms' model' U')) := by
  induction Hto with
  | exit ms model x8 U hsvc hx8 hU =>
    intro Hh Hlazy evs st Hss
    obtain ⟨-, hst⟩ := sstep_exit_inv segs ms model x8 evs st Hh hsvc hx8 Hss
    refine ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model, hst, Or.inl ?_⟩
    simp [m_halted_with_halted]
  | step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy evs st Hss
    obtain ⟨-, hst⟩ := sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep Hss
    refine ⟨ms', model, hst, Or.inr ⟨Hh, Hlazy, U, hto⟩⟩
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro Hh Hlazy evs st Hss
    obtain ⟨eff, model', hspec, -, hst⟩ :=
      sstep_fsys_inv segs ms model x8 evs st Hh Hlazy hsvc hne hshape Hss
    obtain ⟨-, hh', hlazy'⟩ := hshape eff model' [] hspec
    exact ⟨_, model', hst, Or.inr ⟨hh', hlazy', T eff model', hcont eff model' [] hspec⟩⟩

/- -------------------------------------------------------------------------
   No-error characterization.
   ------------------------------------------------------------------------- -/

/-- The invariant of a file-copying run: halted, or still running with a
    `to_fout` node and no lazy mapping. -/
def fon_path (segs : List Segment) (c : config) : Prop :=
  (m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧
    ∃ U, to_fout segs c.cfg_ms c.cfg_model U) ∨
  m_halted c.cfg_model ≠ none

theorem fon_path_step (segs : List Segment) (c : config) (evs : List event)
    (c' : config) (Hop : fon_path segs c) (Hss : sstep segs c evs (.SNext c')) :
    fon_path segs c' := by
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases Hop with ⟨Hh, Hlazy, U, Hto⟩ | Hh
  · obtain ⟨ms'', model'', hst, hcase⟩ :=
      to_fout_progress segs ms model U Hto Hh Hlazy evs _ Hss
    cases hst
    rcases hcase with hhz | ⟨hhz, hlazy', U', Hto'⟩
    · exact Or.inr hhz
    · exact Or.inl ⟨hhz, hlazy', U', Hto'⟩
  · exfalso
    cases Hss with
    | instr ms0 model0 ms0' model0' hh _ _ => exact Hh hh
    | syscall ms0 model0 x8 eff model' model'' evs' hh _ _ _ _ => exact Hh hh
    | exit ms0 model0 x8 eff model' evs' code hh _ _ _ _ => exact Hh hh
    | killed ms0 model0 x8 eff model' evs' sig hh _ _ _ => exact Hh hh

theorem fon_path_no_error (segs : List Segment) (c : config) (evs : List event)
    (Hop : fon_path segs c) : ¬ sstep segs c evs .SError := by
  obtain ⟨ms, model⟩ := c
  intro Hss
  rcases Hop with ⟨Hh, Hlazy, U, Hto⟩ | Hh
  · obtain ⟨ms'', model'', hst, -⟩ :=
      to_fout_progress segs ms model U Hto Hh Hlazy evs _ Hss
    exact step_to.noConfusion hst
  · cases Hss with
    | instr_fault ms0 model0 hh _ _ => exact Hh hh
    | instr_unmodeled ms0 model0 hh _ _ => exact Hh hh
    | syscall_materialization_fault ms0 model0 x8 eff model' evs' hh _ _ _ _ => exact Hh hh
    | syscall_unmodeled ms0 model0 x8 hh _ _ => exact Hh hh

theorem star_fon_path (segs : List Segment) (c : config) (tr : List event)
    (c' : config) (Hop : fon_path segs c) (Hstar : star segs c tr c') :
    fon_path segs c' :=
  star_inv segs (fon_path segs) (fon_path_step segs) c tr c' Hop Hstar

theorem to_fout_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ¬ reaches_error segs ⟨ms, model⟩ := by
  apply exec_no_error
  refine exec_conseq segs ⟨ms, model⟩ (fout_post U) never_errors
    (to_fout_exec segs ms model U Hto Hh Hlazy) ?_
  intro tr o H
  obtain ⟨out, -, -, Hx⟩ := H
  exact exits_with_never_errors out.1 tr o Hx

/- -------------------------------------------------------------------------
   Escape plumbing: reach a syscall-Unmodeled through a star with silent
   syscalls.
   ------------------------------------------------------------------------- -/

theorem star_syscall_nil (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model' : Model)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' []))
    (Hh' : m_halted model' = none) (Hlazy : m_vm_lazy model' = []) :
    star segs ⟨ms, model⟩ [] ⟨advance_past_svc (apply_effect ms eff), model'⟩ := by
  refine star_one segs _ _ _ ?_
  exact sstep.syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
    (by rw [materialize_model_accesses_no_lazy model' _ Hlazy])

theorem reaches_error_star (segs : List Segment) (c : config) (tr : List event)
    (c' : config) (Hstar : star segs c tr c') (Herr : reaches_error segs c') :
    reaches_error segs c := by
  obtain ⟨tr2, c2, evs, Hstar2, Hss⟩ := Herr
  exact ⟨tr ++ tr2, c2, evs, star_trans segs c tr c' Hstar tr2 c2 Hstar2, Hss⟩

theorem spec_err_error (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model .unmodeled) :
    reaches_error segs ⟨ms, model⟩ :=
  ⟨[], ⟨ms, model⟩, [], star.refl _, sstep.syscall_unmodeled ms model x8 Hh Hsvc Hspec⟩

theorem msteps_spec_err_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hm : msteps segs ms ms') (Hsvc : ms'.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms' x8) model .unmodeled) :
    reaches_error segs ⟨ms, model⟩ :=
  reaches_error_star segs ⟨ms, model⟩ [] ⟨ms', model⟩
    (msteps_star_nil segs ms ms' model Hh Hlazy Hm)
    (spec_err_error segs ms' model x8 Hh Hsvc Hspec)

/-- A syscall configuration whose relational spec is `Unmodeled` has no
    successful successor.  Completeness of the executable checker makes
    that exclusion explicit: `CheckUnmodeled` for every proposed effect
    cannot simultaneously be `CheckOk`. -/
theorem spec_err_all_traces_error (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model .unmodeled) :
    all_traces_error segs ⟨ms, model⟩ := by
  have Hno_ok : ∀ (eff : SyscallEffect) (model' : Model) (events : List event),
      ¬ Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' events) := by
    intro eff model' events Hok
    have h1 := check_syscall_complete_unmodeled (sys_input segs ms x8) model eff Hspec
    have h2 := check_syscall_complete_ok (sys_input segs ms x8) eff model model' events Hok
    rw [h1] at h2
    exact check_result.noConfusion h2
  have Hno_next : ∀ (evs : List event) (st : step_to),
      sstep segs ⟨ms, model⟩ evs st → st = .SError := by
    intro evs st Hss
    cases Hss with
    | instr ms0 model0 ms0' model0' hh hsvc hacc => simp_all
    | instr_fault ms0 model0 hh hsvc hacc => simp_all
    | instr_unmodeled ms0 model0 hh hsvc hacc => simp_all
    | syscall ms0 model0 x8' eff model' model'' evs hh hsvc hspec hh' hmat =>
      exfalso
      have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
      rw [hx8] at hspec
      exact Hno_ok eff model' evs hspec
    | syscall_materialization_fault ms0 model0 x8' eff model' evs hh hsvc hspec hh' hmat =>
      rfl
    | exit ms0 model0 x8' eff model' evs code hh hsvc hspec hh' hk =>
      exfalso
      have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
      rw [hx8] at hspec
      exact Hno_ok eff model' evs hspec
    | killed ms0 model0 x8' eff model' evs sig hh hsvc hspec hk =>
      exfalso
      have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
      rw [hx8] at hspec
      exact Hno_ok eff model' evs hspec
    | syscall_unmodeled ms0 model0 x8' hh hsvc hspec => rfl
  refine all_traces_error.intro ⟨ms, model⟩ ⟨[], .SError, ?_⟩ ?_
  · exact sstep.syscall_unmodeled ms model x8 Hh Hsvc Hspec
  · intro evs c' Hnext
    have hse := Hno_next evs (.SNext c') Hnext
    exact absurd hse (by simp)

/-- Deterministic ordinary instructions followed by a syscall-spec
    `Unmodeled` prove the universal source escape, not merely existential
    reachability. -/
theorem msteps_spec_err_all_traces_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (x8 : word) (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = []) (Hm : msteps segs ms ms')
    (Hsvc : ms'.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms' x8) model .unmodeled) :
    all_traces_error segs ⟨ms, model⟩ :=
  msteps_all_traces_error segs ms ms' model Hh Hlazy Hm
    (spec_err_all_traces_error segs ms' model x8 Hh Hsvc Hspec)

/- -------------------------------------------------------------------------
   Ergonomic nodes.
   ------------------------------------------------------------------------- -/

/-- Exit leaf with a small literal code. -/
theorem tfo_exit_code (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 code : word) (Hsvc : ms.ms_svc_pending = some x8) (Hx8 : is_exit_no x8)
    (Hg : ms_gpr ms 0 = code) (Hland : code &&& BitVec.ofInt 64 255 = code) :
    to_fout segs ms model (fun o => o = (code, m_fs model)) := by
  refine to_fout.exit ms model x8 (fun o => o = (code, m_fs model)) Hsvc Hx8 ?_
  intro o
  rw [Hg, Hland]

/-- A syscall with a UNIQUE admissible outcome (file read/write, close,
    open-ENOENT): sequential composition. -/
theorem tfo_sys_det (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model' : Model)
    (U : (word × Fs.Fs) → Prop) (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' []))
    (Huniq : ∀ (eff2 : SyscallEffect) (m2 : Model) (evs2 : List event),
      Specs.syscall_spec (sys_input segs ms x8) model (.ok eff2 m2 evs2) →
      eff2 = eff ∧ m2 = model' ∧ evs2 = [])
    (Hne : ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled)
    (Hh' : m_halted model' = none) (Hlazy' : m_vm_lazy model' = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms eff)) model' U) :
    to_fout segs ms model U := by
  refine to_fout.sys ms model x8 (fun _ _ => U) U Hsvc Hne ⟨eff, model', [], Hok⟩ ?_ ?_ ?_
  · intro eff2 m2 evs2 Hs
    obtain ⟨-, rfl, rfl⟩ := Huniq eff2 m2 evs2 Hs
    exact ⟨rfl, Hh', Hlazy'⟩
  · intro eff2 m2 evs2 Hs
    obtain ⟨rfl, rfl, -⟩ := Huniq eff2 m2 evs2 Hs
    exact Hcont
  · intro o
    constructor
    · intro Ho
      exact ⟨eff, model', [], Hok, Ho⟩
    · rintro ⟨e2, m2, ev2, -, Ht⟩
      exact Ht

/- =========================================================================
   Syscall decoding through the verified checker
   ========================================================================= -/

/- ----- dispatch (Int-characterized syscall numbers) ----- -/

theorem check_syscall_56 (segs : List Segment) (ms : machine_state) (x8 : word)
    (eff : SyscallEffect) (m : Model) (Hno : (x8.toNat : Int) = 56) :
    Checks.ExecutableSpecs.check_syscall (sys_input segs ms x8) eff m
      = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
          (ms_gpr ms 2) eff m := by
  have h : Checks.Sys.Dispatch.lookup_ca Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some Checks.Sys.Dispatch.arm_openat := by
    rw [in_sysno_si, Hno]
    arm_dispatch
  simp only [Checks.ExecutableSpecs.check_syscall, Checks.Sys.Dispatch.CheckedTable.check_syscall,
    Checks.Sys.Dispatch.check_syscall, h, Checks.Sys.Dispatch.ca_check_arm_openat]
  rw [in_arg0_si, in_arg1_si, in_arg2_si]

theorem check_syscall_57 (segs : List Segment) (ms : machine_state) (x8 : word)
    (eff : SyscallEffect) (m : Model) (Hno : (x8.toNat : Int) = 57) :
    Checks.ExecutableSpecs.check_syscall (sys_input segs ms x8) eff m
      = check_close (fd32 (ms_gpr ms 0)) eff m := by
  have h : Checks.Sys.Dispatch.lookup_ca Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some Checks.Sys.Dispatch.arm_close := by
    rw [in_sysno_si, Hno]
    arm_dispatch
  simp only [Checks.ExecutableSpecs.check_syscall, Checks.Sys.Dispatch.CheckedTable.check_syscall,
    Checks.Sys.Dispatch.check_syscall, h, Checks.Sys.Dispatch.ca_check_arm_close]
  rw [in_arg0_si]

theorem check_syscall_63 (segs : List Segment) (ms : machine_state) (x8 : word)
    (eff : SyscallEffect) (m : Model) (Hno : (x8.toNat : Int) = 63) :
    Checks.ExecutableSpecs.check_syscall (sys_input segs ms x8) eff m
      = check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
          (ms_gpr ms 2) eff m := by
  have h : Checks.Sys.Dispatch.lookup_ca Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some Checks.Sys.Dispatch.arm_read := by
    rw [in_sysno_si, Hno]
    arm_dispatch
  simp only [Checks.ExecutableSpecs.check_syscall, Checks.Sys.Dispatch.CheckedTable.check_syscall,
    Checks.Sys.Dispatch.check_syscall, h, Checks.Sys.Dispatch.ca_check_arm_read]
  rw [in_arg0_si, in_arg1_si, in_arg2_si]

theorem check_syscall_64 (segs : List Segment) (ms : machine_state) (x8 : word)
    (eff : SyscallEffect) (m : Model) (Hno : (x8.toNat : Int) = 64) :
    Checks.ExecutableSpecs.check_syscall (sys_input segs ms x8) eff m
      = check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
          (ms_gpr ms 2) eff m := by
  have h : Checks.Sys.Dispatch.lookup_ca Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some Checks.Sys.Dispatch.arm_write := by
    rw [in_sysno_si, Hno]
    arm_dispatch
  simp only [Checks.ExecutableSpecs.check_syscall, Checks.Sys.Dispatch.CheckedTable.check_syscall,
    Checks.Sys.Dispatch.check_syscall, h, Checks.Sys.Dispatch.ca_check_arm_write]
  rw [in_arg0_si, in_arg1_si, in_arg2_si]

/- ----- open-result algebra ----- -/

/-- An in-range fd is never an error-encoded return. -/
theorem fd_not_error (fd : word) (H : (fd.toNat : Int) < 2 ^ 31) :
    addr_is_error_b fd = false := by
  unfold addr_is_error_b two_pow_64
  rw [decide_eq_false_iff_not]
  omega

/-- Recover the errno from an errno-encoded return value. -/
theorem errno_ret_recover (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    two_pow_64 - ((errno_ret e).toNat : Int) = e := by
  rw [errno_ret_unsigned e H1 H2]
  omega

/-- Membership and range facts for openat's injectable errno set. -/
theorem ENOMEM_in_Sys.Fs.Open.openat_errnos : ENOMEM ∈ Sys.Fs.Open.openat_errnos := by
  decide

/--  name (`FileSim:1093`) for the membership fact above.  The
    first declared it with the owning module in the name because
    `openat_errnos` lives in `Sys.Fs.Open`; both names denote the same
    statement. -/
theorem ENOMEM_in_openat_errnos : ENOMEM ∈ Sys.Fs.Open.openat_errnos :=
  ENOMEM_in_Sys.Fs.Open.openat_errnos

theorem openat_errno_range (e : Int) (HIn : e ∈ Sys.Fs.Open.openat_errnos) :
    1 ≤ e ∧ e ≤ 4095 :=
  errnos_ok_range Sys.Fs.Open.openat_errnos e (by decide) HIn

theorem check_open_result_never_unmodeled (eff : SyscallEffect) (m : Model)
    (mk : word → Model) :
    check_open_result eff m mk ≠ .CheckUnmodeled :=
  Checks.Sys.Fs.Open.check_new_fd_result_no_unmodeled Sys.Fs.Open.openat_errnos eff m mk

theorem check_open_result_ok_iff (eff : SyscallEffect) (m : Model)
    (mk : word → Model) (m' : Model) (evs : List event) :
    check_open_result eff m mk = .CheckOk m' evs ↔
      ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧
          m' = m ∧ evs = []) ∨
       (∃ fd, fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m) ∧
          eff = mkEffect fd [] [] ∧ m' = mk fd ∧ evs = [])) := by
  have hret_of : ∀ (ret : word) (ws : List (word × List byte)) (zs : List (word × word))
      (us : List (word × word)) (cs : List MemCopy) (copyins : List (word × Nat))
      (r : word),
      (⟨ret, ws, zs, us, cs, copyins⟩ : SyscallEffect) = mkEffect r [] [] → ret = r := by
    intro ret ws zs us cs copyins r h
    have hh := h
    simp only [mkEffect, SyscallEffect.mkEffectU.injEq] at hh
    exact hh.1
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins
  · simp only [check_open_result, check_new_fd_result]
    by_cases he : errno_ret_in Sys.Fs.Open.openat_errnos ret = true
    · rw [ite_eq_left he]
      constructor
      · intro H
        simp only [check_result.CheckOk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        obtain ⟨e, hmem, heq⟩ := (errno_ret_in_true _ ret).mp he
        exact Or.inl ⟨e, hmem, by rw [heq], rfl, rfl⟩
      · rintro (⟨e, hmem, heff, rfl, rfl⟩ | ⟨fd, hlk, hfd, heff, rfl, rfl⟩)
        · rfl
        · exfalso
          have hret : ret = fd := hret_of _ _ _ _ _ _ _ heff
          rw [hret, hfd, errno_ret_in_alloc_fd _ _ (by decide)] at he
          exact Bool.noConfusion he
    · by_cases hlk : fd_lookup (m_fds m) ret = none
      · by_cases hb : bv_eqb ret (alloc_fd (m_fds m)) = true
        · rw [ite_eq_right he, hlk, ite_eq_left hb]
          constructor
          · intro H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨rfl, rfl⟩ := H
            exact Or.inr ⟨ret, hlk, (bv_eqb_eq ret _).mp hb, rfl, rfl, rfl⟩
          · rintro (⟨x, hmem, heff, rfl, rfl⟩ | ⟨fd, hlk2, hfd, heff, rfl, rfl⟩)
            · exfalso
              have hret : ret = errno_ret x := hret_of _ _ _ _ _ _ _ heff
              exact he (by rw [hret]; exact errno_ret_in_intro _ x hmem)
            · have hret : ret = fd := hret_of _ _ _ _ _ _ _ heff
              rw [hret]
        · rw [ite_eq_right he, hlk, ite_eq_right hb]
          constructor
          · intro H
            exact absurd H (by simp)
          · rintro (⟨x, hmem, heff, rfl, rfl⟩ | ⟨fd, hlk2, hfd, heff, rfl, rfl⟩)
            · exfalso
              have hret : ret = errno_ret x := hret_of _ _ _ _ _ _ _ heff
              exact he (by rw [hret]; exact errno_ret_in_intro _ x hmem)
            · exfalso
              have hret : ret = fd := hret_of _ _ _ _ _ _ _ heff
              rw [hret, hfd] at hb
              rw [bv_eqb_true] at hb
              exact absurd rfl hb
      · obtain ⟨fde, hfdv⟩ : ∃ fde : FdEntry, fd_lookup (m_fds m) ret = some fde := by
          cases h : fd_lookup (m_fds m) ret with
          | none => exact absurd h hlk
          | some e => exact ⟨e, rfl⟩
        rw [ite_eq_right he, hfdv]
        change (check_result.CheckReject = check_result.CheckOk m' evs ↔ _)
        constructor
        · intro H
          exact absurd H (by simp)
        · rintro (⟨x, hmem, heff, rfl, rfl⟩ | ⟨fd, hlk2, hfd, heff, rfl, rfl⟩)
          · exfalso
            have hret : ret = errno_ret x := hret_of _ _ _ _ _ _ _ heff
            exact he (by rw [hret]; exact errno_ret_in_intro _ x hmem)
          · exfalso
            have hret : ret = fd := hret_of _ _ _ _ _ _ _ heff
            rw [← hret, hfdv] at hlk2
            exact absurd hlk2 (by simp)
  all_goals simp [check_open_result, check_new_fd_result, mkEffect]

/-- The pathname copy-in range an `openat` records: one read of the path
    pointer, through the first NUL (or `path_max`). -/
def open_copyins (ms : machine_state) : List (word × Nat) :=
  [(ms_gpr ms 1, cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]

def check_open_result_copyins (reads : List (word × Nat)) (eff : SyscallEffect)
    (m : Model) (mk : word → Model) : check_result :=
  check_copyins reads eff (check_open_result (clear_copyins eff) m mk)

theorem effect_from_copyins_and_clear (eff : SyscallEffect) (reads : List (word × Nat))
    (core : SyscallEffect) (Hreads : eff.eff_copyins = reads)
    (Hcore : clear_copyins eff = core) : eff = with_copyins reads core := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  simp only at Hreads
  subst Hreads
  simp only [clear_copyins, with_copyins] at Hcore ⊢
  cases Hcore
  rfl

theorem check_open_result_copyins_never_unmodeled (reads : List (word × Nat))
    (eff : SyscallEffect) (m : Model) (mk : word → Model) :
    check_open_result_copyins reads eff m mk ≠ .CheckUnmodeled := by
  intro H
  unfold check_open_result_copyins check_copyins at H
  by_cases hr : access_ranges_eqb eff.eff_copyins reads = true
  · rw [ite_eq_left hr] at H
    exact check_open_result_never_unmodeled (clear_copyins eff) m mk H
  · rw [ite_eq_right hr] at H
    exact absurd H (by simp)

theorem check_open_result_copyins_ok_iff (reads : List (word × Nat))
    (eff : SyscallEffect) (m : Model) (mk : word → Model) (m' : Model)
    (evs : List event) :
    check_open_result_copyins reads eff m mk = .CheckOk m' evs ↔
      ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧
          eff = with_copyins reads (mkEffect (errno_ret e) [] []) ∧
          m' = m ∧ evs = []) ∨
       (∃ fd, fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m) ∧
          eff = with_copyins reads (mkEffect fd [] []) ∧ m' = mk fd ∧ evs = [])) := by
  unfold check_open_result_copyins check_copyins
  by_cases hr : access_ranges_eqb eff.eff_copyins reads = true
  · rw [ite_eq_left hr]
    have hreads : eff.eff_copyins = reads := (access_ranges_eqb_eq _ _).mp hr
    rw [check_open_result_ok_iff]
    constructor
    · rintro (⟨e, hmem, hcore, rfl, rfl⟩ | ⟨fd, hlk, hfd, hcore, rfl, rfl⟩)
      · exact Or.inl ⟨e, hmem, effect_from_copyins_and_clear eff reads _ hreads hcore, rfl, rfl⟩
      · exact Or.inr ⟨fd, hlk, hfd, effect_from_copyins_and_clear eff reads _ hreads hcore, rfl, rfl⟩
    · rintro (⟨e, hmem, heff, rfl, rfl⟩ | ⟨fd, hlk, hfd, heff, rfl, rfl⟩)
      · refine Or.inl ⟨e, hmem, ?_, rfl, rfl⟩
        rw [heff]
        simp only [clear_copyins, with_copyins]
      · refine Or.inr ⟨fd, hlk, hfd, ?_, rfl, rfl⟩
        rw [heff]
        simp only [clear_copyins, with_copyins]
  · rw [ite_eq_right hr]
    constructor
    · intro H
      exact absurd H (by simp)
    · rintro (⟨e, -, heff, -, -⟩ | ⟨fd, -, -, heff, -, -⟩)
      · rw [heff] at hr
        simp only [with_copyins, access_ranges_eqb_refl] at hr
        exact False.elim (hr trivial)
      · rw [heff] at hr
        simp only [with_copyins, access_ranges_eqb_refl] at hr
        exact False.elim (hr trivial)

theorem check_copyins_after_ret_only (reads : List (word × Nat)) (eff : SyscallEffect)
    (r : word) (m : Model) (evs : List event) :
    check_copyins_after reads eff (check_ret_only (clear_copyins eff) r m evs)
      = check_ret_only_copyins reads eff r m evs := by
  unfold check_copyins_after check_ret_only_copyins
  cases h : check_ret_only (clear_copyins eff) r m evs with
  | CheckOk m' evs' => rfl
  | CheckReject => simp only [check_copyins]; split <;> rfl
  | CheckUnmodeled =>
    exact absurd h (check_ret_only_no_unmodeled (clear_copyins eff) r m evs)

/- =========================================================================
   The modeled open shapes: the checker reduced to an `open` node

   Each open node below needs the same three steps out of `check_openat`:
   the pathname fetch (`check_openat_body`'s three-way `match`), the dirfd
   gate, and the flag dispatch (`check_openat_resolved`).  They are proved
   once here as rewrite lemmas, so the nodes carry only the hypotheses a
   caller can know.
   ========================================================================= -/

/-- The `CstrOk` branch of the pathname fetch: the three-way `match` the
    body opens with collapses to the branch the hypotheses select. -/
theorem check_openat_body_cstrOk (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (p : Fs.path)
    (Hpath : read_cstr i.in_mem pathp = .CstrOk p) :
    check_openat_body i dirfd pathp flags eff m
      = (if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
         else if !(bv_eqb dirfd Sys.Uapi.AT_FDCWD32) then .CheckUnmodeled
         else check_openat_resolved p flags eff m) := by
  unfold check_openat_body
  rw [Hpath]

/-- ... and its non-empty variant: the empty pathname is -ENOENT by fiat,
    so a `path_eqb p [] = false` premise removes that arm. -/
theorem check_openat_body_cstrOk_nonempty (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (p : Fs.path)
    (Hpath : read_cstr i.in_mem pathp = .CstrOk p) (Hpe : path_eqb p [] = false) :
    check_openat_body i dirfd pathp flags eff m
      = (if !(bv_eqb dirfd Sys.Uapi.AT_FDCWD32) then .CheckUnmodeled
         else check_openat_resolved p flags eff m) := by
  rw [check_openat_body_cstrOk i dirfd pathp flags eff m p Hpath, Hpe]
  simp only [Bool.false_eq_true, ite_false]

/-- ... and the AT_FDCWD variant: with the dirfd test passing, the body IS
    the resolved-path dispatch. -/
theorem check_openat_body_resolved (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) (p : Fs.path)
    (Hpath : read_cstr i.in_mem pathp = .CstrOk p) (Hpe : path_eqb p [] = false)
    (Hdirfd : bv_eqb dirfd Sys.Uapi.AT_FDCWD32 = true) :
    check_openat_body i dirfd pathp flags eff m = check_openat_resolved p flags eff m := by
  rw [check_openat_body_cstrOk_nonempty i dirfd pathp flags eff m p Hpath Hpe, Hdirfd]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]

/-- The `O_RDONLY` lane of `check_openat_resolved`: on a separator-free
    pathname the flag chain lands on the read arm. -/
theorem check_openat_resolved_rd (p : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model)
    (Hslash : Sys.Fs.Open.path_has_slash p = false)
    (Hfl : Sys.Fs.File.z_ldiff ((flags.toNat : Int))
             Sys.Fs.Open.open_ignored_flags = (0 : Int)) :
    check_openat_resolved p flags eff m = check_openat_read p eff m := by
  have h0 : ((0 : Int) == (0 : Int)) = true := by decide
  -- `Hfl` names the alias `Sys.Fs.File.z_ldiff`; the body it must rewrite
  -- speaks `Sys.Uapi.z_ldiff`, the definition the alias stands for.
  simp only [Sys.Fs.File.z_ldiff] at Hfl
  unfold check_openat_resolved
  dsimp only
  rw [Hslash, Hfl, h0]
  simp only [Bool.false_eq_true, ite_false, ite_true]

/-- The `O_WRONLY|O_CREAT|O_TRUNC` lane of `check_openat_resolved`.  The
    ground guards are decided once here (`by decide` on the flag word), so
    the two write-create nodes below carry no arithmetic. -/
theorem check_openat_resolved_wr_create (p : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model)
    (Hslash : Sys.Fs.Open.path_has_slash p = false)
    (Hfl : Sys.Fs.File.z_ldiff ((flags.toNat : Int))
             Sys.Fs.Open.open_ignored_flags = Sys.Fs.Open.wr_create_flags) :
    check_openat_resolved p flags eff m = check_openat_create p eff m := by
  have h0 : (Sys.Fs.Open.wr_create_flags == (0 : Int)) = false := by decide
  have h1 : (Sys.Fs.Open.wr_create_flags == Sys.Fs.Open.wr_create_flags) = true := by decide
  -- as above: unfold the alias named in `Hfl` to the definition the body uses.
  simp only [Sys.Fs.File.z_ldiff] at Hfl
  unfold check_openat_resolved
  dsimp only
  rw [Hslash, Hfl, h0, h1]
  simp only [Bool.false_eq_true, ite_false, ite_true]

/-- The copy-in leg of `check_openat`, discharged once: the body's result is
    an `open`-result check, which never declines, so `check_copyins_after`
    composes to `check_copyins` and the goal is the
    `check_open_result_copyins` the nodes carry. -/
theorem check_copyins_after_open (reads : List (word × Nat)) (eff : SyscallEffect)
    (m : Model) (mk : word → Model) :
    check_copyins_after reads eff (check_open_result (clear_copyins eff) m mk)
      = check_open_result_copyins reads eff m mk := by
  unfold check_open_result_copyins
  cases h : check_open_result (clear_copyins eff) m mk with
  | CheckOk m' evs' => rfl
  | CheckReject => rfl
  | CheckUnmodeled =>
    exact absurd h (check_open_result_never_unmodeled (clear_copyins eff) m mk)

/-- An over-PATH_MAX path reduces the checker to the deterministic
    -ENAMETOOLONG return, with NO dirfd hypothesis: `openat_spec` fetches
    the pathname before it resolves the dirfd, exactly as Linux's
    `getname()` runs before `path_init`'s `fdget_raw`.  The FLAG word is
    still required, because `build_open_flags()` runs BEFORE `getname()`:
    a combination the model does not interpret is declined before the
    pathname is ever looked at. -/
theorem openat_toolong_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (Hno : (x8.toNat : Int) = 56)
    (Hfl : Sys.Fs.Open.modeled_open_flags (ms_gpr ms 2) = true)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrTooLong)
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model
      = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENAMETOOLONG) model [] := by
  rw [check_syscall_56 segs ms x8 eff model Hno]
  unfold Checks.Sys.Fs.Open.check_openat
  rw [Hfl]
  simp only [Bool.not_true]
  unfold check_openat_body
  rw [in_mem_si, Hpath]
  exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret ENAMETOOLONG) model []

/-- The two modeled open shapes reduce the checker to `check_open_result`
    with the respective success-model builder. -/
theorem openat_rd_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : Fs.path) (d : List byte) (Hno : (x8.toNat : Int) = 56)
    (Hdirfd : ms_gpr ms 0 = Sys.Uapi.AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : Sys.Fs.File.z_ldiff ((ms_gpr ms 2).toNat : Int)
             Sys.Fs.Open.open_ignored_flags = (0 : Int))
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = some d) (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model
      = check_open_result_copyins (open_copyins ms) eff model
          (fun fd => with_fds (fd_insert (m_fds model) fd
                         (FdEntry.FdFile p (BitVec.ofInt 64 0))) model) := by
  have Hunw := Sys.Fs.Open.openat_plain_name_noslash p Hdot
  have Hnd := Sys.Fs.Open.openat_plain_name_nodirref p Hdot
  have hd : bv_eqb (fd32 (ms_gpr ms 0)) Sys.Uapi.AT_FDCWD32 = true := by
    rw [Hdirfd]
    exact bv_eqb_true _
  rw [check_syscall_56 segs ms x8 eff model Hno]
  unfold Checks.Sys.Fs.Open.check_openat
  rw [Sys.Fs.Open.modeled_open_flags_rd _ Hfl]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [check_openat_body_resolved (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
    (ms_gpr ms 1) (ms_gpr ms 2) (clear_copyins eff) model p
    (by rw [in_mem_si]; exact Hpath) Hpe hd]
  rw [check_openat_resolved_rd p (ms_gpr ms 2) (clear_copyins eff) model Hunw Hfl]
  unfold check_openat_read
  rw [Hnd, Hfs]
  rw [in_mem_si]
  exact check_copyins_after_open (open_copyins ms) eff model _

/-- The write-create open of a plain name NOTHING LIVES UNDER: the branch
    set of a create.  The `fs_under` premise is the image-side half of what
    `openat_plain_name` says about the path: a plain name some key lives
    under is an implied directory, and the create arm answers it -EISDIR
    instead (`openat_wr_isdir_check`). -/
theorem openat_wr_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : Fs.path) (Hno : (x8.toNat : Int) = 56)
    (Hdirfd : ms_gpr ms 0 = Sys.Uapi.AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : Sys.Fs.File.z_ldiff ((ms_gpr ms 2).toNat : Int)
             Sys.Fs.Open.open_ignored_flags = Sys.Fs.Open.wr_create_flags)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hun : Sys.Fs.Open.fs_under (m_fs model) p = false) (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model
      = check_open_result_copyins (open_copyins ms) eff model
          (fun fd => with_fds (fd_insert (m_fds model) fd
                         (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
                       (with_fs (fs_set (m_fs model) p []) model)) := by
  have Hunw := Sys.Fs.Open.openat_plain_name_noslash p Hdot
  have Hnd := Sys.Fs.Open.openat_plain_name_nodirref p Hdot
  have hd : bv_eqb (fd32 (ms_gpr ms 0)) Sys.Uapi.AT_FDCWD32 = true := by
    rw [Hdirfd]
    exact bv_eqb_true _
  rw [check_syscall_56 segs ms x8 eff model Hno]
  unfold Checks.Sys.Fs.Open.check_openat
  rw [Sys.Fs.Open.modeled_open_flags_wr _ Hfl]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [check_openat_body_resolved (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
    (ms_gpr ms 1) (ms_gpr ms 2) (clear_copyins eff) model p
    (by rw [in_mem_si]; exact Hpath) Hpe hd]
  rw [check_openat_resolved_wr_create p (ms_gpr ms 2) (clear_copyins eff) model Hunw Hfl]
  unfold check_openat_create check_create_wronly
  rw [Hnd, Hun]
  simp only [Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
  rw [in_mem_si]
  exact check_copyins_after_open (open_copyins ms) eff model _

/-- The write-create open of a plain name SOME KEY LIVES UNDER: the
    checker reduces to the deterministic -EISDIR return, and the model is
    untouched.  `Sys.Fs.Open.openat_create_spec` carries the derivation
    (`do_open`'s `d_is_dir` on the positive dentry the lookup finds,
    fs/namei.c, Linux v6.18.46); this is the proof-side handle on it, the
    twin of `openat_wr_check` for the image the other cannot take. -/
theorem openat_wr_isdir_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (p : Fs.path) (Hno : (x8.toNat : Int) = 56)
    (Hdirfd : ms_gpr ms 0 = Sys.Uapi.AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hfl : Sys.Fs.File.z_ldiff ((ms_gpr ms 2).toNat : Int)
             Sys.Fs.Open.open_ignored_flags = Sys.Fs.Open.wr_create_flags)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hun : Sys.Fs.Open.fs_under (m_fs model) p = true) (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model
      = check_ret_only_copyins (open_copyins ms) eff (errno_ret EISDIR) model [] := by
  have Hunw := Sys.Fs.Open.openat_plain_name_noslash p Hdot
  have Hnd := Sys.Fs.Open.openat_plain_name_nodirref p Hdot
  have hd : bv_eqb (fd32 (ms_gpr ms 0)) Sys.Uapi.AT_FDCWD32 = true := by
    rw [Hdirfd]
    exact bv_eqb_true _
  rw [check_syscall_56 segs ms x8 eff model Hno]
  unfold Checks.Sys.Fs.Open.check_openat
  rw [Sys.Fs.Open.modeled_open_flags_wr _ Hfl]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [check_openat_body_resolved (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
    (ms_gpr ms 1) (ms_gpr ms 2) (clear_copyins eff) model p
    (by rw [in_mem_si]; exact Hpath) Hpe hd]
  rw [check_openat_resolved_wr_create p (ms_gpr ms 2) (clear_copyins eff) model Hunw Hfl]
  unfold check_openat_create
  rw [Hnd, Hun]
  simp only [Bool.or_true, Bool.false_eq_true, ite_false, ite_true]
  rw [in_mem_si]
  exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret EISDIR) model []

/- =========================================================================
   Open nodes: core, then the four concrete open shapes
   ========================================================================= -/

/- The effect projections the open nodes' `T` reads: a copy-in list does
   not move the return value. -/
theorem with_copyins_eff_ret_errno (reads : List (word × Nat)) (e : Int) :
    (with_copyins reads (mkEffect (errno_ret e) [] [])).eff_ret = errno_ret e := rfl

theorem with_copyins_eff_ret_fd (reads : List (word × Nat)) (fd : word) :
    (with_copyins reads (mkEffect fd [] [])).eff_ret = fd := rfl

/-- Core open node over an abstract success-model builder `mk`.  Errnos
    are `Int` (`Te : Int → _`); fds are `word`s below `2^31`. -/
theorem tfo_open_core (segs : List Segment) (ms : machine_state) (model : Model)
    (mk : word → Model) (x8 : word) (reads : List (word × Nat))
    (Te : Int → (word × Fs.Fs) → Prop) (Ts : word → (word × Fs.Fs) → Prop)
    (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk)
    (Hmk : ∀ fd, m_halted (mk fd) = none ∧ m_vm_lazy (mk fd) = [])
    (Herr : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       to_fout segs (advance_past_svc (apply_effect ms
         (with_copyins reads (mkEffect (errno_ret e) [] [])))) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
       to_fout segs (advance_past_svc (apply_effect ms
         (with_copyins reads (mkEffect fd [] [])))) (mk fd) (Ts fd))
    (HU : ∀ o, U o ↔
       ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ Te e o) ∨
        (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)
           ∧ Ts fd o))) :
    to_fout segs ms model U := by
  refine to_fout.sys ms model x8
    (fun eff _ => if addr_is_error_b (eff.eff_ret)
       then Te (two_pow_64 - ((eff.eff_ret).toNat : Int)) else Ts (eff.eff_ret))
    U Hsvc ?_ ?_ ?_ ?_ ?_
  · -- no Unmodeled
    intro Hspec
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hspec
    rw [Hchk] at hc
    exact check_open_result_copyins_never_unmodeled reads _ model mk hc
  · -- receptive: ENOMEM
    refine ⟨with_copyins reads (mkEffect (errno_ret ENOMEM) [] []), model, [], ?_⟩
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk, check_open_result_copyins_ok_iff]
    exact Or.inl ⟨ENOMEM, ENOMEM_in_Sys.Fs.Open.openat_errnos, rfl, rfl, rfl⟩
  · -- shape
    intro eff model' evs Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_open_result_copyins_ok_iff] at Hs
    rcases Hs with ⟨e, -, rfl, rfl, rfl⟩ | ⟨fd, -, -, rfl, rfl, rfl⟩
    · exact ⟨rfl, Hh, Hlazy⟩
    · exact ⟨rfl, (Hmk fd).1, (Hmk fd).2⟩
  · -- continuations
    intro eff model' evs Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_open_result_copyins_ok_iff] at Hs
    rcases Hs with ⟨e, hmem, rfl, rfl, -⟩ | ⟨fd, hlk, heq, rfl, rfl, -⟩
    · obtain ⟨h1, h2⟩ := openat_errno_range e hmem
      rw [with_copyins_eff_ret_errno, errno_ret_error_b e h1 h2,
        errno_ret_recover e h1 h2]
      simp only [ite_true]
      exact Herr e hmem
    · have hne : addr_is_error_b fd = false := by
        rw [heq]
        exact alloc_fd_not_error_b _
      rw [with_copyins_eff_ret_fd, hne]
      simp only [Bool.false_eq_true, ite_false]
      exact Hok fd hlk heq
  · -- outcome set
    intro o
    rw [HU o]
    constructor
    · rintro (⟨e, hmem, hT⟩ | ⟨fd, hlk, heq, hT⟩)
      · obtain ⟨h1, h2⟩ := openat_errno_range e hmem
        refine ⟨with_copyins reads (mkEffect (errno_ret e) [] []), model, [], ?_, ?_⟩
        · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
            check_open_result_copyins_ok_iff]
          exact Or.inl ⟨e, hmem, rfl, rfl, rfl⟩
        · rw [with_copyins_eff_ret_errno, errno_ret_error_b e h1 h2,
            errno_ret_recover e h1 h2]
          simp only [ite_true]
          exact hT
      · have hne : addr_is_error_b fd = false := by
          rw [heq]
          exact alloc_fd_not_error_b _
        refine ⟨with_copyins reads (mkEffect fd [] []), mk fd, [], ?_, ?_⟩
        · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
            check_open_result_copyins_ok_iff]
          exact Or.inr ⟨fd, hlk, heq, rfl, rfl, rfl⟩
        · rw [with_copyins_eff_ret_fd, hne]
          simp only [Bool.false_eq_true, ite_false]
          exact hT
    · rintro ⟨eff, model', evs, hspec, hT⟩
      rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
        check_open_result_copyins_ok_iff] at hspec
      rcases hspec with ⟨e, hmem, rfl, rfl, -⟩ | ⟨fd, hlk, heq, rfl, rfl, -⟩
      · obtain ⟨h1, h2⟩ := openat_errno_range e hmem
        left
        refine ⟨e, hmem, ?_⟩
        rw [with_copyins_eff_ret_errno, errno_ret_error_b e h1 h2,
          errno_ret_recover e h1 h2] at hT
        simpa only [ite_true] using hT
      · have hne : addr_is_error_b fd = false := by
          rw [heq]
          exact alloc_fd_not_error_b _
        right
        refine ⟨fd, hlk, heq, ?_⟩
        /- Rewritten in the step of its own, as the mirror arm above does:
           folded into one `simpa`, `hne` has to fire inside the `ite`'s
           `Decidable` argument, and this toolchain's `simpa` leaves `hT`
           at `if addr_is_error_b fd = true then … else …`. -/
        rw [with_copyins_eff_ret_fd, hne] at hT
        simpa only [Bool.false_eq_true, ite_false] using hT

/-- A concrete successful open resolution (used by the escape path). -/
theorem open_ok_fd (segs : List Segment) (ms : machine_state) (model : Model)
    (mk : word → Model) (x8 : word) (reads : List (word × Nat)) (fd : word)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk)
    (Hlk : fd_lookup (m_fds model) fd = none) (Hlt : fd = alloc_fd (m_fds model)) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (with_copyins reads (mkEffect fd [] [])) (mk fd) []) := by
  rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
    check_open_result_copyins_ok_iff]
  exact Or.inr ⟨fd, Hlk, Hlt, rfl, rfl, rfl⟩

/-- A deterministic syscall node whose checker is a `check_ret_only_copyins`
    leaf (open -ENOENT / -EISDIR / -ENAMETOOLONG): the three side goals of
    `tfo_sys_det`, discharged once. -/
theorem tfo_sys_det_ret_only_copyins (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word) (reads : List (word × Nat)) (ret : word)
    (U : (word × Fs.Fs) → Prop) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
              = check_ret_only_copyins reads eff ret model [])
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (with_copyins reads (mkEffect ret [] [])))) model U) :
    to_fout segs ms model U := by
  refine tfo_sys_det segs ms model x8 (with_copyins reads (mkEffect ret [] [])) model U
    Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
  · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_ret_only_copyins_ok_iff] at Hs
    exact Hs
  · intro Hs
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hs
    rw [Hchk] at hc
    exact check_ret_only_copyins_no_unmodeled reads _ ret model [] hc

/-- The same, for a `check_ret_only` leaf (close). -/
theorem tfo_sys_det_ret_only (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word) (ret : word) (model' : Model)
    (U : (word × Fs.Fs) → Prop) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
              = check_ret_only eff ret model' [])
    (Hh : m_halted model' = none) (Hlazy : m_vm_lazy model' = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (mkEffect ret [] []))) model' U) :
    to_fout segs ms model U := by
  refine tfo_sys_det segs ms model x8 (mkEffect ret [] []) model' U
    Hsvc ?_ ?_ ?_ Hh Hlazy Hcont
  · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk, check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk, check_ret_only_ok_iff] at Hs
    exact Hs
  · intro Hs
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hs
    rw [Hchk] at hc
    exact check_ret_only_no_unmodeled _ ret model' [] hc

/-- An over-PATH_MAX pathname: deterministic -ENAMETOOLONG, whatever the
    dirfd is, for any flag word the model interprets.  The model says what
    Linux says. -/
theorem tfo_openat_toolong (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 56)
    (Hfl : Sys.Fs.Open.modeled_open_flags (ms_gpr ms 2) = true)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrTooLong)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (with_copyins (open_copyins ms)
         (mkEffect (errno_ret ENAMETOOLONG) [] [])))) model U) :
    to_fout segs ms model U :=
  tfo_sys_det_ret_only_copyins segs ms model x8 (open_copyins ms)
    (errno_ret ENAMETOOLONG) U Hsvc
    (openat_toolong_check segs ms x8 model Hno Hfl Hpath) Hh Hlazy Hcont

/-- O_RDONLY open of an absent file: deterministic -ENOENT.  Two paths
    reach it — the empty pathname is -ENOENT by fiat, any other by the
    absent lookup — and both are the same leaf, so the node needs no
    `path_eqb p [] = false` premise. -/
theorem tfo_openat_enoent (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 56)
    (Hdirfd : ms_gpr ms 0 = Sys.Uapi.AT_FDCWD)
    (Hpath : read_cstr (ms_read_byte ms) (ms_gpr ms 1) = .CstrOk p)
    (Hfl : Sys.Fs.File.z_ldiff ((ms_gpr ms 2).toNat : Int)
             Sys.Fs.Open.open_ignored_flags = (0 : Int))
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = none)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] [])))) model U) :
    to_fout segs ms model U := by
  have Hunw := Sys.Fs.Open.openat_plain_name_noslash p Hdot
  have Hnd := Sys.Fs.Open.openat_plain_name_nodirref p Hdot
  have hd : bv_eqb (fd32 (ms_gpr ms 0)) Sys.Uapi.AT_FDCWD32 = true := by
    rw [Hdirfd]
    exact bv_eqb_true _
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [] := by
    intro eff
    rw [check_syscall_56 segs ms x8 eff model Hno]
    unfold Checks.Sys.Fs.Open.check_openat
    rw [Sys.Fs.Open.modeled_open_flags_rd _ Hfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hpe : path_eqb p [] = false
    · rw [check_openat_body_resolved (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
        (ms_gpr ms 1) (ms_gpr ms 2) (clear_copyins eff) model p
        (by rw [in_mem_si]; exact Hpath) hpe hd]
      rw [check_openat_resolved_rd p (ms_gpr ms 2) (clear_copyins eff) model Hunw Hfl]
      unfold check_openat_read
      rw [Hnd, Hfs]
      rw [in_mem_si]
      exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret ENOENT) model []
    · have hpe' : path_eqb p [] = true := by
        cases h : path_eqb p [] with
        | false => exact absurd h hpe
        | true => rfl
      rw [check_openat_body_cstrOk (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
        (ms_gpr ms 1) (ms_gpr ms 2) (clear_copyins eff) model p
        (by rw [in_mem_si]; exact Hpath), hpe']
      simp only [ite_true]
      rw [in_mem_si]
      exact check_copyins_after_ret_only (open_copyins ms) eff (errno_ret ENOENT) model []
  exact tfo_sys_det_ret_only_copyins segs ms model x8 (open_copyins ms)
    (errno_ret ENOENT) U Hsvc Hchk Hh Hlazy Hcont

/-- close: deterministic, removes the fd. -/
theorem tfo_close (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (e : FdEntry) (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 57)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some e)
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (mkEffect (BitVec.ofInt 64 0) [] [])))
       (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) U) :
    to_fout segs ms model U := by
  have Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = check_ret_only eff (BitVec.ofInt 64 0)
          (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) [] := by
    intro eff
    rw [check_syscall_57 segs ms x8 eff model Hno]
    unfold Checks.Sys.Fs.Open.check_close
    rw [Hfd32, Hfd]
  exact tfo_sys_det_ret_only segs ms model x8 (BitVec.ofInt 64 0)
    (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) U Hsvc Hchk Hh Hlazy Hcont

/- `BitVec.ofInt 64` round-trips a `word`'s unsigned value —
   `Z_to_bv_bv_unsigned`, the canonical
   `BvBase.ofInt_toNat`, imported and opened here. -/

/-- A checked-success `if` over a guard: the shape the `FdFile` read and
    the `FdFileW` write arms both end in. -/
theorem check_guard_checkOk_iff (C : Bool) (M m2 : Model) (evs : List event) :
    (if C then (.CheckOk M [] : check_result) else .CheckReject) = .CheckOk m2 evs ↔
      (C = true ∧ m2 = M ∧ evs = []) := by
  cases C with
  | false =>
    simp only [Bool.false_eq_true, ite_false, check_result.CheckOk.noConfusion]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨h, -, -⟩
      exact absurd h (by simp)
  | true =>
    simp only [ite_true, check_result.CheckOk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨trivial, rfl, rfl⟩
    · rintro ⟨-, rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/-- The read arm's delivery guard, read as the effect it accepts:
    `1 ≤ length bs` and the claimed write is exactly the delivered bytes at
    the buffer, with the return the delivered length. -/
theorem read_guard_iff (a ret buf : word) (bs' : List byte) (b : byte) (bsr : List byte) :
    ((bv_eqb a buf && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))
        = true ↔
      (⟨ret, [(a, bs')], [], [], [], []⟩ : SyscallEffect)
        = mkEffect (len_word (b :: bsr)) [(buf, b :: bsr)] []) := by
  constructor
  · intro H
    simp only [Bool.and_eq_true] at H
    obtain ⟨⟨ha, hbs⟩, hret⟩ := H
    rw [bv_eqb_eq] at ha hret
    rw [listN_eqb_eq] at hbs
    simp only [mkEffect, ha, hbs, hret]
  · intro H
    have hret : ret = len_word (b :: bsr) := by
      have := congrArg SyscallEffect.eff_ret H
      simpa [mkEffect] using this
    have hws : [(a, bs')] = [(buf, b :: bsr)] := by
      have := congrArg SyscallEffect.eff_writes H
      simpa [mkEffect] using this
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hws
    obtain ⟨rfl, rfl⟩ := hws
    have hbsr : listN_eqb (b :: bsr) (b :: bsr) = true := (listN_eqb_eq _ _).mpr rfl
    rw [hret, PropExec.bv_eqb_refl, hbsr, PropExec.bv_eqb_refl]
    rfl

/-- A file read through the checker: deterministic, and the outcome set of
    the checker is exactly the one `tfo_read_file` carries. -/
theorem check_read_file (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (off : word) (data w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFile p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Haok : access_okb (ms_gpr ms 1) ((ms_gpr ms 2).toNat : Int) = true)
    (HL : ((len_word (file_read data off (ms_gpr ms 2))).toNat : Int)
             ≤ ((ms_gpr ms 2).toNat : Int))
    (eff : SyscallEffect) (m2 : Model) (evs : List event) :
    check_syscall (sys_input segs ms x8) eff model = .CheckOk m2 evs ↔
      (eff = mkEffect (len_word (file_read data off (ms_gpr ms 2)))
              (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) []
       ∧ m2 = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                (FdEntry.FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model
       ∧ evs = []) := by
  have hcl := rw_count_clamp_of_rw (ms_gpr ms 2) Hcnt
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  rw [check_syscall_63 segs ms x8 ⟨ret, ws, zs, us, cs, copyins⟩ model Hno]
  simp only [Checks.Sys.Fs.ReadWrite.check_read, Hfd32, Hfd, Haok, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [hcl, ofInt_toNat]
  simp only [Hfs, in_wmem_si]
  rw [read_bytes_map_prefix (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2)
    (len_word (file_read data off (ms_gpr ms 2))) w HL Hw]
  simp only []
  cases hbs : file_read data off (ms_gpr ms 2) with
  | nil =>
    rw [hbs] at *
    simp only [delivered_writes, len_word]
    rw [check_ret_only_ok_iff]
    simp only [mkEffect]
    exact Iff.rfl
  | cons b bsr =>
    rw [hbs] at *
    cases ws with
    | nil => simp [mkEffect, delivered_writes]
    | cons hd tl =>
      obtain ⟨a, bs'⟩ := hd
      cases tl with
      | cons _ _ => simp [mkEffect, delivered_writes]
      | nil =>
        cases zs with
        | cons _ _ => simp [mkEffect, delivered_writes]
        | nil =>
          cases us with
          | cons _ _ => simp [mkEffect, delivered_writes]
          | nil =>
            cases cs with
            | cons _ _ => simp [mkEffect, delivered_writes]
            | nil =>
              cases copyins with
              | cons _ _ => simp [mkEffect, delivered_writes]
              | nil =>
                simp only [delivered_writes]
                rw [check_guard_checkOk_iff, read_guard_iff]

/-- The read checker, once the pathname/lookup/fd hypotheses hold, never
    says `Unmodeled` — the `Hne` side goal of the deterministic read node. -/
theorem check_read_file_not_unmodeled (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word) (p : Fs.path) (off : word) (data w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFile p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Haok : access_okb (ms_gpr ms 1) ((ms_gpr ms 2).toNat : Int) = true)
    (HL : ((len_word (file_read data off (ms_gpr ms 2))).toNat : Int)
             ≤ ((ms_gpr ms 2).toNat : Int))
    (eff : SyscallEffect) :
    check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled := by
  have hcl := rw_count_clamp_of_rw (ms_gpr ms 2) Hcnt
  rw [check_syscall_63 segs ms x8 eff model Hno]
  simp only [Checks.Sys.Fs.ReadWrite.check_read, Hfd32, Hfd, Haok, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [hcl, ofInt_toNat]
  simp only [Hfs, in_wmem_si]
  rw [read_bytes_map_prefix (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2)
    (len_word (file_read data off (ms_gpr ms 2))) w HL Hw]
  simp only []
  split
  · exact check_ret_only_no_unmodeled _ _ _ _
  · split <;> simp
  · simp

/-- The `!` of a `Bool` in the form the guards write it. -/
theorem not_of_true {b : Bool} (h : b = true) : (!b) = false := by rw [h]; rfl

theorem not_of_false {b : Bool} (h : b = false) : (!b) = true := by rw [h]; rfl

/-- The delivered-length bound: a file read never delivers more bytes than
    the count named. -/
theorem len_word_file_read_le (data : List byte) (off count : word) :
    ((len_word (file_read data off count)).toNat : Int) ≤ (count.toNat : Int) := by
  have h1 : (file_read data off count).length ≤ count.toNat := by
    rw [length_file_read]
    exact Nat.min_le_left _ _
  have h2 : (file_read data off count).length < 2 ^ 64 := by
    have h3 := count.isLt
    omega
  unfold len_word
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
  omega

/-- File read of `cnt` bytes: deterministic, fills the buffer, advances the
    offset. -/
theorem tfo_read_file (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (off : word) (data w : List byte)
    (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFile p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = some w)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Hpos : 0 < ((ms_gpr ms 2).toNat : Int))
    (Haok : access_okb (ms_gpr ms 1) ((ms_gpr ms 2).toNat : Int) = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                 (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) [])))
       (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
          (FdEntry.FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model) U) :
    to_fout segs ms model U := by
  have HL := len_word_file_read_le data off (ms_gpr ms 2)
  refine tfo_sys_det segs ms model x8 _ _ U Hsvc ?_ ?_ ?_ ?_ ?_ Hcont
  · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff]
    exact (check_read_file segs ms model x8 p off data w Hno Hfd Hfd32 Hfs Hw Hcnt Haok HL
      _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff] at Hs
    exact (check_read_file segs ms model x8 p off data w Hno Hfd Hfd32 Hfs Hw Hcnt Haok HL
      eff2 m2 evs2).mp Hs
  · intro Hs
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hs
    exact check_read_file_not_unmodeled segs ms model x8 p off data w Hno Hfd Hfd32 Hfs Hw
      Hcnt Haok HL _ hc
  · exact Hh
  · exact Hlazy

/-- A file write through the checker, positive count: the deterministic
    `check_ret_only_copyins` leaf whose ledger is the readable prefix. -/
theorem check_write_file_w (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (off : word) (data bs : List byte)
    (Hno : (x8.toNat : Int) = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : Sys.Fs.ReadWrite.modeled_file_gap data off bs = true)
    (Hnz : w_is0 (ms_gpr ms 2) = false) :
    ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = check_ret_only_copyins [(ms_gpr ms 1, bs.length)] eff (ms_gpr ms 2)
          (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
             (FdEntry.FdFileW p (off + ms_gpr ms 2)))
             (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2)
      = some bs := by
    rw [in_mem_si]
    exact Hrd
  have Hlen := read_bytes_map_length (sys_input segs ms x8).in_mem (ms_gpr ms 1)
    (ms_gpr ms 2) bs hrb
  have Hret : len_word bs = ms_gpr ms 2 := by
    have h1 : bs.length = (ms_gpr ms 2).toNat := by omega
    unfold len_word
    rw [h1]
    exact ofInt_toNat _
  have Hgate : (!(w_is0 (ms_gpr ms 2)) && (bs.length == 0)) = false := by
    rw [not_of_false Hnz, Bool.true_and]
    by_cases h0 : bs.length = 0
    · exfalso
      have hcount0 : ms_gpr ms 2 = BitVec.ofInt 64 0 := by
        rw [← Hret]
        unfold len_word
        rw [h0]
        rfl
      rw [hcount0] at Hnz
      exact Bool.noConfusion Hnz
    · cases h : (bs.length == 0) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) h0
  have hrange : modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2) = true := by
    unfold modeled_rw_range modeled_rw_count
    rw [decide_eq_true Hcnt]
    rfl
  have hrr : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = false :=
    not_of_true hrange
  have hgap' : (!(Sys.Fs.ReadWrite.modeled_file_gap data off bs)) = false :=
    not_of_true Hgap
  intro eff
  rw [check_syscall_64 segs ms x8 eff model Hno]
  simp only [Checks.Sys.Fs.ReadWrite.check_write, Hfd32, Hfd, in_mem_si, hrr,
    Bool.false_eq_true, ite_false]
  rw [write_source_of_rw (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) Hcnt,
    readable_bytes_full (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) bs Hrd]
  simp only [Hgate, Bool.false_eq_true, ite_false]
  simp only [Hfs]
  simp only [hgap', Bool.false_eq_true, ite_false]
  rw [Hnz]
  simp only [Bool.false_eq_true, ite_false]
  rw [Hret]

/-- File write: deterministic full write of the readable buffer bytes. -/
theorem tfo_write_file (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (off : word) (data bs : List byte)
    (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : Sys.Fs.ReadWrite.modeled_file_gap data off bs = true)
    (Hnz : w_is0 (ms_gpr ms 2) = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (with_copyins [(ms_gpr ms 1, bs.length)] (mkEffect (ms_gpr ms 2) [] []))))
       (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
          (FdEntry.FdFileW p (off + ms_gpr ms 2)))
          (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U) :
    to_fout segs ms model U := by
  have Hchk := check_write_file_w segs ms model x8 p off data bs Hno Hfd Hfd32 Hrd Hcnt Hfs
    Hgap Hnz
  refine tfo_sys_det segs ms model x8 _ _ U Hsvc ?_ ?_ ?_ ?_ ?_ Hcont
  · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_ret_only_copyins_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_ret_only_copyins_ok_iff] at Hs
    exact Hs
  · intro Hs
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hs
    rw [Hchk] at hc
    exact check_ret_only_copyins_no_unmodeled _ _ _ _ _ hc
  · exact Hh
  · exact Hlazy

/-- The `count = 0` half of `tfo_write_file`: no user byte is read, so the
    effect carries no copy-in range at all (the checker rejects a singleton
    zero-length one), and `access_ok`'s range verdict is the whole of what
    the write does. -/
theorem check_write_file_zero (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (off : word) (data bs : List byte)
    (Hno : (x8.toNat : Int) = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : Sys.Fs.ReadWrite.modeled_file_gap data off bs = true)
    (Hz : w_is0 (ms_gpr ms 2) = true)
    (Hok : access_okb (ms_gpr ms 1) ((ms_gpr ms 2).toNat : Int) = true) :
    ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = check_ret_only eff (ms_gpr ms 2)
          (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
             (FdEntry.FdFileW p (off + ms_gpr ms 2)))
             (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) [] := by
  have hrb : read_bytes_map (sys_input segs ms x8).in_mem (ms_gpr ms 1) (ms_gpr ms 2)
      = some bs := by
    rw [in_mem_si]
    exact Hrd
  have Hlen := read_bytes_map_length (sys_input segs ms x8).in_mem (ms_gpr ms 1)
    (ms_gpr ms 2) bs hrb
  have Hret : len_word bs = ms_gpr ms 2 := by
    have h1 : bs.length = (ms_gpr ms 2).toNat := by omega
    unfold len_word
    rw [h1]
    exact ofInt_toNat _
  have hrange : modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2) = true := by
    unfold modeled_rw_range modeled_rw_count
    rw [decide_eq_true Hcnt]
    rfl
  have hrr : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = false :=
    not_of_true hrange
  have hgap' : (!(Sys.Fs.ReadWrite.modeled_file_gap data off bs)) = false :=
    not_of_true Hgap
  have Hgate : (!(w_is0 (ms_gpr ms 2)) && (bs.length == 0)) = false := by
    rw [not_of_true Hz]
    rfl
  intro eff
  rw [check_syscall_64 segs ms x8 eff model Hno]
  simp only [Checks.Sys.Fs.ReadWrite.check_write, Hfd32, Hfd, in_mem_si, hrr,
    Bool.false_eq_true, ite_false]
  rw [write_source_of_rw (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) Hcnt,
    readable_bytes_full (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) bs Hrd]
  simp only [Hgate, Bool.false_eq_true, ite_false]
  simp only [Hfs]
  simp only [hgap', Bool.false_eq_true, ite_false]
  rw [Hz]
  simp only [ite_true]
  unfold Checks.Sys.Uaccess.check_access_ok_zero
  rw [Hok]
  simp only [ite_true]
  rw [Hret]

/-- The `count = 0` write node: no user byte moves, so the effect is the
    bare zero-length copy-in-free return, and the model changes exactly as
    in `tfo_write_file`. -/
theorem tfo_write_file_zero (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (p : Fs.path) (off : word) (data bs : List byte)
    (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 64)
    (Hfd : fd_lookup (m_fds model) (ms_gpr ms 0) = some (FdEntry.FdFileW p off))
    (Hfd32 : fd32 (ms_gpr ms 0) = ms_gpr ms 0)
    (Hrd : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some bs)
    (Hcnt : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : Sys.Fs.ReadWrite.modeled_file_gap data off bs = true)
    (Hz : w_is0 (ms_gpr ms 2) = true)
    (Hok : access_okb (ms_gpr ms 1) ((ms_gpr ms 2).toNat : Int) = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (advance_past_svc (apply_effect ms
       (mkEffect (ms_gpr ms 2) [] [])))
       (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
          (FdEntry.FdFileW p (off + ms_gpr ms 2)))
          (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U) :
    to_fout segs ms model U := by
  have Hchk := check_write_file_zero segs ms model x8 p off data bs Hno Hfd Hfd32 Hrd Hcnt
    Hfs Hgap Hz Hok
  refine tfo_sys_det segs ms model x8 _ _ U Hsvc ?_ ?_ ?_ ?_ ?_ Hcont
  · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk, check_ret_only_ok_iff]
    exact ⟨rfl, rfl, rfl⟩
  · intro eff2 m2 evs2 Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk, check_ret_only_ok_iff] at Hs
    exact Hs
  · intro Hs
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hs
    rw [Hchk] at hc
    exact check_ret_only_no_unmodeled _ _ _ _ hc
  · exact Hh
  · exact Hlazy

/-- `arg_reg_0/1/2` at the `Nat`-cast index `record_gpr` produces. -/
theorem rec_arg_0 : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide

theorem rec_arg_1 : BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide

theorem rec_arg_2 : BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) := by decide

/-- Reading a raw ecall record's argument registers: the `ms_gpr`
    projection of the record shape `step_ecall` leaves. -/
theorem record_gpr (regs : BvMap word) (fr : BvMap word) (pc : word) (sv : Option word)
    (rv : Option word) (fc : BitVec 32) (mem rom : word → Option byte) (k : Nat) :
    ms_gpr { ms_regs := regs, ms_fregs := fr, ms_pc_val := pc, ms_svc_pending := sv,
             ms_resv := rv, ms_fcsr := fc, ms_mem := mem, ms_rom := rom } k
      = reg_get regs (BitVec.ofInt 5 (10 + (k : Int))) := rfl

/-! ### Ergonomic "at the raw ecall record" wrappers

    Per-binary proofs need not reprove the `ms_gpr` projections at every
    fd/read/write/open/close/exit call site.  The records carry the ecall
    post-state shape `step_ecall` leaves: `ms_svc_pending := some (getr
    regs 17)`, `ms_resv := none`; register hypotheses are `reg_get regs
    10/11/12` (a0/a1/a2), and the syscall number is Int-characterized
    (`((getr regs 17).toNat : Int) = ...`).
 This tree names it once as `erec` — the ekall
    record, `mkst`'s counterpart for the pre-advance state — so each
    statement below reads like the one without repeating eight
    fields, and a caller whose state is the literal record matches by
    computation (`erec` is a `def`). -/

/-- The raw ecall record: the machine state `step_ecall` leaves before
    the model advance. -/
def erec (regs : BvMap word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
    ms_svc_pending := some (getr regs 17), ms_resv := none,
    ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom }

theorem erec_svc_pending (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    (erec regs pc mem rom).ms_svc_pending = some (getr regs 17) := rfl

theorem erec_read_byte (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) :
    ms_read_byte (erec regs pc mem (seg_rom segs)) = mrb segs mem := rfl

theorem erec_gpr_0 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (erec regs pc mem rom) 0 = reg_get regs 10 := by
  unfold erec
  rw [record_gpr, rec_arg_0]

theorem erec_gpr_1 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (erec regs pc mem rom) 1 = reg_get regs 11 := by
  unfold erec
  rw [record_gpr, rec_arg_1]

theorem erec_gpr_2 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (erec regs pc mem rom) 2 = reg_get regs 12 := by
  unfold erec
  rw [record_gpr, rec_arg_2]

/-- Exit leaf. -/
theorem tfo_exit_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (code : word) (fsv : Fs.Fs)
    (H17 : ((getr regs 17).toNat : Int) = 93) (H10 : reg_get regs 10 = code)
    (Hc : (code.toNat : Int) < 256) (Hfs : m_fs model = fsv) :
    to_fout segs (erec regs pc mem rom) model (fun o => o = (code, fsv)) := by
  subst Hfs
  refine tfo_exit_code segs _ model (getr regs 17) code rfl (Or.inl H17) ?_ ?_
  · rw [erec_gpr_0]
    exact H10
  · exact land_255_small code Hc

/-- File read of `cnt` bytes: deterministic, fills the buffer, advances the
    offset. -/
theorem tfo_read_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (fdv : word) (p : Fs.path)
    (off : word) (data : List byte) (buf cnt : word) (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 63)
    (H10 : reg_get regs 10 = fdv) (H11 : reg_get regs 11 = buf)
    (H12 : reg_get regs 12 = cnt)
    (Hfd : fd_lookup (m_fds model) fdv = some (FdEntry.FdFile p off))
    (Hfd32 : fd32 fdv = fdv)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hwseg : StreamSim.wseg_ok segs buf (word_to_nat cnt) = true)
    (Hcnt : (cnt.toNat : Int) ≤ rw_bytes_max) (Hpos : 0 < (cnt.toNat : Int))
    (Haok : access_okb buf (cnt.toNat : Int) = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
        (write_to_mem mem buf (file_read data off cnt)) rom)
      (with_fds (fd_insert (m_fds model) fdv
        (FdEntry.FdFile p (off + len_word (file_read data off cnt)))) model) U) :
    to_fout segs (erec regs pc mem rom) model U := by
  have Hg0 : ms_gpr (erec regs pc mem rom) 0 = fdv := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem rom) 1 = buf := by
    rw [erec_gpr_1]; exact H11
  have Hg2 : ms_gpr (erec regs pc mem rom) 2 = cnt := by
    rw [erec_gpr_2]; exact H12
  obtain ⟨w, Hw⟩ := StreamSim.wseg_ok_wdef segs buf cnt (erec regs pc mem rom) Hwseg
  have Hfd' : fd_lookup (m_fds model) (ms_gpr (erec regs pc mem rom) 0)
      = some (FdEntry.FdFile p off) := by rw [Hg0]; exact Hfd
  have Hfd32' : fd32 (ms_gpr (erec regs pc mem rom) 0)
      = ms_gpr (erec regs pc mem rom) 0 := by rw [Hg0]; exact Hfd32
  have Hw' : read_bytes_map (ms_writable_byte segs (erec regs pc mem rom))
      (ms_gpr (erec regs pc mem rom) 1) (ms_gpr (erec regs pc mem rom) 2) = some w := by
    rw [Hg1, Hg2]; exact Hw
  have Hcnt' : ((ms_gpr (erec regs pc mem rom) 2).toNat : Int) ≤ rw_bytes_max := by
    rw [Hg2]; exact Hcnt
  have Haok' : access_okb (ms_gpr (erec regs pc mem rom) 1)
      ((ms_gpr (erec regs pc mem rom) 2).toNat : Int) = true := by
    rw [Hg1, Hg2]; exact Haok
  have Hpos' : 0 < ((ms_gpr (erec regs pc mem rom) 2).toNat : Int) := by
    rw [Hg2]; exact Hpos
  refine tfo_read_file segs (erec regs pc mem rom) model (getr regs 17) p off data w U
    rfl H17 Hfd' Hfd32' Hfs Hw' Hcnt' Hpos' Haok' Hh Hlazy ?_
  rw [Hg0, Hg1, Hg2]
  simp only [erec, StreamExec.adv_apply_delivered]
  exact Hcont

/-- File write: deterministic full write of the readable buffer bytes. -/
theorem tfo_write_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (fdv : word) (p : Fs.path)
    (off : word) (data bs : List byte) (buf cnt : word) (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 64)
    (H10 : reg_get regs 10 = fdv) (H11 : reg_get regs 11 = buf)
    (H12 : reg_get regs 12 = cnt)
    (Hfd : fd_lookup (m_fds model) fdv = some (FdEntry.FdFileW p off))
    (Hfd32 : fd32 fdv = fdv)
    (Hrd : rdn segs mem buf (word_to_nat cnt) = some bs)
    (Hcnt : (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hfs : fs_lookup (m_fs model) p = some data)
    (Hgap : Sys.Fs.ReadWrite.modeled_file_gap data off bs = true)
    (Hok : access_okb buf (cnt.toNat : Int) = true ∨ 0 < (cnt.toNat : Int))
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
      (with_fds (fd_insert (m_fds model) fdv (FdEntry.FdFileW p (off + cnt)))
         (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U) :
    to_fout segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = fdv := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = buf := by
    rw [erec_gpr_1]; exact H11
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = cnt := by
    rw [erec_gpr_2]; exact H12
  have Hrd' : read_bytes_map (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1)
      (ms_gpr (erec regs pc mem (seg_rom segs)) 2) = some bs := by
    rw [Hg1, Hg2, read_bytes_map_read_byte,
      ms_read_bytes_rdn segs (erec regs pc mem (seg_rom segs)) buf cnt rfl]
    exact Hrd
  have Hfd' : fd_lookup (m_fds model) (ms_gpr (erec regs pc mem (seg_rom segs)) 0)
      = some (FdEntry.FdFileW p off) := by rw [Hg0]; exact Hfd
  have Hfd32' : fd32 (ms_gpr (erec regs pc mem (seg_rom segs)) 0)
      = ms_gpr (erec regs pc mem (seg_rom segs)) 0 := by rw [Hg0]; exact Hfd32
  have Hcnt' : ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      ≤ rw_bytes_max := by rw [Hg2]; exact Hcnt
  cases hz : w_is0 cnt with
  | false =>
    have Hnz : w_is0 (ms_gpr (erec regs pc mem (seg_rom segs)) 2) = false := by
      rw [Hg2]; exact hz
    refine tfo_write_file segs (erec regs pc mem (seg_rom segs)) model (getr regs 17) p off
      data bs U rfl H17 Hfd' Hfd32' Hrd' Hcnt' Hfs Hgap Hnz Hh Hlazy ?_
    rw [Hg0, Hg2]
    simp only [erec, StreamExec.adv_apply_delivered]
    exact Hcont
  | true =>
    have Hz : w_is0 (ms_gpr (erec regs pc mem (seg_rom segs)) 2) = true := by
      rw [Hg2]; exact hz
    have Hoka : access_okb (ms_gpr (erec regs pc mem (seg_rom segs)) 1)
        ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int) = true := by
      rcases Hok with h | h
      · rw [Hg1, Hg2]; exact h
      · exfalso
        rw [w_is0_pos cnt (by omega)] at hz
        exact Bool.noConfusion hz
    refine tfo_write_file_zero segs (erec regs pc mem (seg_rom segs)) model (getr regs 17) p
      off data bs U rfl H17 Hfd' Hfd32' Hrd' Hcnt' Hfs Hgap Hz Hoka Hh
      Hlazy ?_
    rw [Hg0, Hg2]
    simp only [erec, adv_eff_ret]
    exact Hcont

/-- close: deterministic, removes the fd. -/
theorem tfo_close_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (fdv : word) (e : FdEntry)
    (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 57) (H10 : reg_get regs 10 = fdv)
    (Hfd : fd_lookup (m_fds model) fdv = some e) (Hfd32 : fd32 fdv = fdv)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (BitVec.ofInt 64 0)) (v_addi pc 4) mem rom)
      (with_fds (fd_remove (m_fds model) fdv) model) U) :
    to_fout segs (erec regs pc mem rom) model U := by
  have Hg0 : ms_gpr (erec regs pc mem rom) 0 = fdv := by
    rw [erec_gpr_0]; exact H10
  have Hfd' : fd_lookup (m_fds model) (ms_gpr (erec regs pc mem rom) 0) = some e := by
    rw [Hg0]; exact Hfd
  have Hfd32' : fd32 (ms_gpr (erec regs pc mem rom) 0)
      = ms_gpr (erec regs pc mem rom) 0 := by rw [Hg0]; exact Hfd32
  refine tfo_close segs (erec regs pc mem rom) model (getr regs 17) e U
    rfl H17 Hfd' Hfd32' Hh Hlazy ?_
  rw [Hg0]
  simp only [erec, adv_eff_ret]
  exact Hcont

/-- O_RDONLY openat of an absent file: deterministic -ENOENT. -/
theorem tfo_open_enoent_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (p : Fs.path) (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (H10 : reg_get regs 10 = Sys.Uapi.AT_FDCWD)
    (H12 : reg_get regs 12 = BitVec.ofInt 64 0)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = none)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = Sys.Uapi.AT_FDCWD := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = BitVec.ofInt 64 0 := by
    rw [erec_gpr_2]; exact H12
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrOk p := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl : Sys.Fs.File.z_ldiff ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      Sys.Fs.Open.open_ignored_flags = (0 : Int) := by
    rw [Hg2]
    decide
  refine tfo_openat_enoent segs (erec regs pc mem (seg_rom segs)) model (getr regs 17) p U
    rfl H17 Hg0 Hpath' Hfl Hdot Hfs Hh Hlazy ?_
  simp only [erec, adv_eff_ret_copyins]
  exact Hcont

/-- O_RDONLY openat of a present file: errno branch or the lowest free
    fd. -/
theorem tfo_open_rd_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (p : Fs.path) (d : List byte)
    (Te : Int → (word × Fs.Fs) → Prop) (Ts : word → (word × Fs.Fs) → Prop)
    (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (H10 : reg_get regs 10 = Sys.Uapi.AT_FDCWD)
    (H12 : reg_get regs 12 = BitVec.ofInt 64 0)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = some d)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))
         model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
       to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
         (with_fds (fd_insert (m_fds model) fd (FdEntry.FdFile p (BitVec.ofInt 64 0))) model)
         (Ts fd))
    (HU : ∀ o, U o ↔
       ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ Te e o) ∨
        (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)
           ∧ Ts fd o))) :
    to_fout segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = Sys.Uapi.AT_FDCWD := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = BitVec.ofInt 64 0 := by
    rw [erec_gpr_2]; exact H12
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrOk p := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl : Sys.Fs.File.z_ldiff ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      Sys.Fs.Open.open_ignored_flags = (0 : Int) := by
    rw [Hg2]
    decide
  refine tfo_open_core segs (erec regs pc mem (seg_rom segs)) model
    (fun fd => with_fds (fd_insert (m_fds model) fd
      (FdEntry.FdFile p (BitVec.ofInt 64 0))) model)
    (getr regs 17) (open_copyins (erec regs pc mem (seg_rom segs))) Te Ts U rfl Hh Hlazy
    ?_ ?_ ?_ ?_ HU
  · intro eff
    exact openat_rd_check segs (erec regs pc mem (seg_rom segs)) (getr regs 17) model p d
      H17 Hg0 Hpath' Hpe Hfl Hdot Hfs eff
  · intro fd
    exact ⟨by rw [with_fds_halted]; exact Hh, Hlazy⟩
  · intro e hmem
    simp only [erec, adv_eff_ret_copyins]
    exact Herr e hmem
  · intro fd hlk hlt
    simp only [erec, adv_eff_ret_copyins]
    exact Hok fd hlk hlt

/-- O_WRONLY|O_CREAT|O_TRUNC openat of a plain name nothing lives under:
    errno branch or create-empty at the lowest free fd. -/
theorem tfo_open_wr_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (p : Fs.path)
    (Te : Int → (word × Fs.Fs) → Prop) (Ts : word → (word × Fs.Fs) → Prop)
    (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (H10 : reg_get regs 10 = Sys.Uapi.AT_FDCWD)
    (H12 : reg_get regs 12 = BitVec.ofInt 64 577)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hun : Sys.Fs.Open.fs_under (m_fs model) p = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))
         model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
       to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
         (with_fds (fd_insert (m_fds model) fd (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
            (with_fs (fs_set (m_fs model) p []) model)) (Ts fd))
    (HU : ∀ o, U o ↔
       ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ Te e o) ∨
        (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)
           ∧ Ts fd o))) :
    to_fout segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = Sys.Uapi.AT_FDCWD := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = BitVec.ofInt 64 577 := by
    rw [erec_gpr_2]; exact H12
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrOk p := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl : Sys.Fs.File.z_ldiff ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      Sys.Fs.Open.open_ignored_flags = Sys.Fs.Open.wr_create_flags := by
    rw [Hg2]
    decide
  refine tfo_open_core segs (erec regs pc mem (seg_rom segs)) model
    (fun fd => with_fds (fd_insert (m_fds model) fd
      (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
      (with_fs (fs_set (m_fs model) p []) model))
    (getr regs 17) (open_copyins (erec regs pc mem (seg_rom segs))) Te Ts U rfl Hh Hlazy
    ?_ ?_ ?_ ?_ HU
  · intro eff
    exact openat_wr_check segs (erec regs pc mem (seg_rom segs)) (getr regs 17) model p
      H17 Hg0 Hpath' Hpe Hfl Hdot Hun eff
  · intro fd
    exact ⟨by rw [with_fds_halted, with_fs_halted]; exact Hh, Hlazy⟩
  · intro e hmem
    simp only [erec, adv_eff_ret_copyins]
    exact Herr e hmem
  · intro fd hlk hlt
    simp only [erec, adv_eff_ret_copyins]
    exact Hok fd hlk hlt

/-- O_WRONLY|O_CREAT|O_TRUNC openat of a plain name SOME KEY LIVES
    UNDER: the deterministic -EISDIR continuation, model untouched. -/
theorem tfo_open_wr_isdir_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (p : Fs.path)
    (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (H10 : reg_get regs 10 = Sys.Uapi.AT_FDCWD)
    (H12 : reg_get regs 12 = BitVec.ofInt 64 577)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hun : Sys.Fs.Open.fs_under (m_fs model) p = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model U) :
    to_fout segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = Sys.Uapi.AT_FDCWD := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = BitVec.ofInt 64 577 := by
    rw [erec_gpr_2]; exact H12
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrOk p := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl : Sys.Fs.File.z_ldiff ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      Sys.Fs.Open.open_ignored_flags = Sys.Fs.Open.wr_create_flags := by
    rw [Hg2]
    decide
  refine tfo_sys_det_ret_only_copyins segs (erec regs pc mem (seg_rom segs)) model
    (getr regs 17) (open_copyins (erec regs pc mem (seg_rom segs)))
    (errno_ret EISDIR) U rfl ?_ Hh Hlazy ?_
  · intro eff
    exact openat_wr_isdir_check segs (erec regs pc mem (seg_rom segs)) (getr regs 17) model p
      H17 Hg0 Hpath' Hpe Hfl Hdot Hun eff
  · simp only [erec, adv_eff_ret_copyins]
    exact Hcont

/-- openat on a path with no NUL within PATH_MAX: -ENAMETOOLONG in a0,
    independent of the dirfd, for any open mode the model interprets
    (`modeled_open_flags` — the kernel validates the flags before it
    fetches the pathname). -/
theorem tfo_open_toolong_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (Hfl : Sys.Fs.Open.modeled_open_flags (reg_get regs 12) = true)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrTooLong)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hcont : to_fout segs
      (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem (seg_rom segs))
      model U) :
    to_fout segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = reg_get regs 12 := erec_gpr_2 ..
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrTooLong := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl' : Sys.Fs.Open.modeled_open_flags
      (ms_gpr (erec regs pc mem (seg_rom segs)) 2) = true := by
    rw [Hg2]
    exact Hfl
  refine tfo_openat_toolong segs (erec regs pc mem (seg_rom segs)) model (getr regs 17) U
    rfl H17 Hfl' Hpath' Hh Hlazy ?_
  simp only [erec, adv_eff_ret_copyins]
  exact Hcont

/- =========================================================================
   Run-level packaging and the equivalence glue
   ========================================================================= -/

/-- The run-level omni judgment of a file-copying run. -/
theorem fout_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (word × Fs.Fs) → Prop)
    (Hto : to_fout segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp (fout_post U) := by
  simpa [omni_run, mkImage, init_config] using
    to_fout_exec segs _ _ U Hto rfl rfl

theorem fout_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (word × Fs.Fs) → Prop)
    (Hto : to_fout segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  intro tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none := rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] := rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨o, Ho, Hp'⟩ :=
      to_fout_star_only segs _ _ U Hto Hh Hlazy tr' c Hstar
    exact ⟨o, Ho, is_prefix_trans Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := to_fout_star_admits segs _ _ U Hto Hh Hlazy o Ho
    exact ⟨fout_trace o, c, Hstar, Hp⟩

theorem fout_no_error_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (word × Fs.Fs) → Prop)
    (Hto : to_fout segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) :=
  to_fout_no_error segs _ _ U Hto rfl rfl

/-- The omni equivalence for two file-copying binaries with the SAME
    outcome set `U`, at the two role budgets. -/
theorem fout_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (U : (word × Fs.Fs) → Prop) (inp : ProcInput)
    (Hsource : to_fout source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U)
    (Htarget : to_fout target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  constructor
  · refine coexec_conseq source_segs _ never_errors (covered source_segs) ?_ ?_
    · exact (bh_errors_iff (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ inp).mp
        (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U
          Hsource)
    · intro tr o h
      exact never_errors_covered source_segs tr o h
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U
        Hsource tr).trans
        (fout_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U
          Htarget tr).symm
    · exact (bh_errors_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp
        (fout_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget)

/-- The `Equivalence`-level equivalence for two file-copying binaries with
    the SAME outcome set `U`. -/
theorem fout_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (U : (word × Fs.Fs) → Prop) (inp : ProcInput)
    (Hsource : to_fout source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_fout target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U) :
    modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp) ∧
    equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
          (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (fout_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource)
  · right
    constructor
    · intro tr
      exact (fout_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).trans
        (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
    · exact fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

/-- SOURCE-ERROR ESCAPE at the `Equivalence` level.  The premise is
    deliberately universal: a chosen `star`/`reaches_error` witness is
    insufficient when another source resolution avoids error. -/
theorem spec_err_escape_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (target : behavior)
    (Hall : all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp)) :
    equiv (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) target :=
  Or.inl Hall
