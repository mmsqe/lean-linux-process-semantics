/-
  * Common.ShapeNodes — syscall NODE rules for [ShapeAlg.realizes]
    carried over:

    Image-INDEPENDENT proof library.

    ** What this file gives you

    [ShapeAlg.realizes segs c T] is proved by following every execution
    path.  Between syscalls the machine is deterministic ([rz_msteps]);
    at each [ecall] the proof must supply a NODE: the exact set of
    admissible successor configurations ([ShapeAlg.node_ok] = complete
    + sound w.r.t. [Run.sstep] / [Specs.syscall_spec]) together with the
    events each resolution emits, and a [realizes] derivation for every
    successor.  This file packages that obligation once per syscall
    shape, in three layers:

    1. GENERIC checker-driven nodes ([node_sys_chk], [rz_sys_chk],
       [rz_ret_chk], ...): the admissible outcomes of the pending
       syscall are read off the VERIFIED executable checker
       [ExecutableSpecs.check_syscall] ([check_syscall_ok_iff] /
       [check_syscall_err_iff]).  A per-syscall rule only has to
       (a) reduce [check_syscall (sys_input segs ms x8) eff model] to a
       small checker expression in [eff] and (b) characterize when that
       expression says [CheckOk].

    2. PER-SYSCALL nodes at the generic machine-state level (any [ms]
       with [ms_svc_pending ms = Some x8], arguments read through
       [ms_gpr ms k]) — the same level as [ShapeAlg.rz_write1] /
       [rz_exit] / [rz_mmap]: [rz_set_tid_*], [rz_openat_*],
       [rz_read_file*], [rz_read_dir], [rz_close*], [rz_ioctl_*],
       [rz_brk_*], [rz_mprotect_*], [rz_mmap_*] ...

    3. [mkst]-LEVEL WRAPPERS (suffix [_at]): the form a symbolic-
       execution proof applies.  Pre-state [mkst regs pc mem rom] sits
       ON the [ecall] instruction ([fetch_word segs pc = Some w],
       [is_ecall w = true], [ms_svc_pending = None]); the rule performs
       BOTH the instruction step (which only sets [ms_svc_pending :=
       Some a7], see [PropExec.step_ecall]) and the syscall transition,
       and hands the continuation the collapsed post-state
       [mkst (regupd regs 10 RET) (v_addi pc 4) mem' rom] with the
       updated model.  Register hypotheses are [getr regs 17 = Z_to_bv
       64 SYSNO], [getr regs 10 = ...] etc.

    ** Conventions

    - Errno returns are [errno_ret e = Z_to_bv 64 (- e)]; the arithmetic
      facts callers branch on are [errno_ret_signed_neg],
      [errno_ret_unsigned_ge], [errno_ret_ne_small].
    - Nondeterministic nodes whose resolutions all continue silently
      come in two flavours: an INDEXED rule (continuation shape may
      depend on the resolution: [t_alt]) and a CONSTANT corollary (all
      resolutions of a group realize the same shape: plain [T] or
      [t_alt2 A B]).  Our programs only test [a0 < 0], so the constant
      corollaries are what per-binary proofs use.
    - [t_alt2 A B] rules REQUIRE both groups inhabited (otherwise the
      shape degenerates); e.g. the mmap success group needs one
      admissible address — see [mmap_addr_exists_*].

    See also the usage notes (a
    cheat-sheet with the exact hypothesis shapes).

  NOTES.

  - `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv 64 z` → `BitVec.ofInt 64 z`,
    `bv_unsigned w` → the `Int`-valued `(w.toNat : Int)`, `bv_signed w` →
    `w.toInt`, `ms_svc_pending`/`ms_gpr`/`ms_read_bytes`/`ms_writable_byte`
    stay the `RiscvSemantics` projections and `Some`/`None` become
    `some`/`none`.
  - `bv_modulus`/`bv_half_modulus` are not in Lean core, so
    this tree defines them at the values `PropExec.bv_swrap` is written
    with (`2^n`, `2^(n-1)`).  Only the two width-64 numerals are used.
  - [errno_ret_ne_small]  is NOT in
    `ShapeNodes`; it lives in the usage notes, so it is not restated here here.
  - Every declaration is proved; the file carries no proof hole, no escape
    hatch and no extra postulate.
-/
import LinuxSem.Common.AgentLib
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.FileSim
import LinuxSem.Common.StreamExec
import LinuxSem.Checks.ExecutableSpecs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Common.PropExec
open LinuxSem.Common.ShapeAlg
open LinuxSem.LinuxProcessSem.RiscvSemantics.machine_state
open LinuxSem.LinuxProcessSem.Sys.Uaccess (delivered_writes)
open LinuxSem.Common.FileSim (mrb adv_eff_ret)
open LinuxSem.Common.CatExec (wbytes adv_set ms_read_bytes_rdn)
open LinuxSem.Common.StreamExec (adv_apply_write adv_apply_delivered)
open LinuxSem.Common.MmapSim (adv_mmap_grant zfill)

namespace LinuxSem.Common.ShapeNodes

/- =========================================================================
   PART 0 — small arithmetic facts about return values
   ========================================================================= -/

/-- The modulus `2^n`, at the value `PropExec.bv_swrap` is written
    with. -/
def bv_modulus (n : Nat) : Int := ((2 ^ n : Nat) : Int)

/-- The half modulus `2^(n-1)`. -/
def bv_half_modulus (n : Nat) : Int := ((2 ^ (n - 1) : Nat) : Int)

/-- Half/modulus constants, as numerals. -/
theorem bv_modulus_64 : bv_modulus 64 = 18446744073709551616 := by decide

theorem bv_half_modulus_64 : bv_half_modulus 64 = 9223372036854775808 := by decide

/-- An errno-encoded return is negative as a signed 64-bit value ... -/
theorem errno_ret_signed_neg (e : Int) (He : 1 ≤ e ∧ e ≤ 4095) :
    (errno_ret e).toInt = -e := by
  unfold errno_ret
  exact AgentLib.bv_signed_neg e ⟨by omega, by omega⟩

/-- ... i.e. its unsigned value is in the top page of the address space. -/
theorem errno_ret_unsigned_ge (e : Int) (He : 1 ≤ e ∧ e ≤ 4095) :
    ((errno_ret e).toNat : Int) = 2 ^ 64 - e := by
  have h : (-e : Int) % 2 ^ 64 = 2 ^ 64 - e := by
    rw [show (-e : Int) = (2 ^ 64 - e) + 2 ^ 64 * (-1) from by omega,
      Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (a := 2 ^ 64 - e) (b := 2 ^ 64) (by omega) (by omega)]
  unfold errno_ret
  rw [BitVec.toNat_ofInt, AgentLib.two_pow64_cast, h, Int.toNat_of_nonneg (by omega)]

/-- A small non-negative value (an fd, a byte count) read as signed. -/
theorem small_signed_nonneg (w : word) (z : Int) (Hw : w = BitVec.ofInt 64 z)
    (Hz : 0 ≤ z ∧ z < 2 ^ 63) : w.toInt = z := by
  subst Hw
  exact AgentLib.bv_signed_small z Hz

theorem Z_to_bv_small_unsigned (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z :=
  AgentLib.u64_lit z Hz

/-- [len_word] of a short list, as unsigned and signed numbers. -/
theorem len_word_unsigned {A : Type} (l : List A)
    (H : ((l.length : Nat) : Int) < 2 ^ 64) :
    ((len_word l).toNat : Int) = l.length := by
  unfold len_word
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem len_word_signed {A : Type} (l : List A)
    (H : ((l.length : Nat) : Int) < 2 ^ 63) : (len_word l).toInt = l.length := by
  have hw : len_word l = BitVec.ofInt 64 ((l.length : Nat) : Int) := by
    unfold len_word
    rw [BitVec.ofInt_natCast]
  exact small_signed_nonneg (len_word l) ((l.length : Nat) : Int) hw ⟨by omega, by omega⟩

theorem word_to_nat_len_word {A : Type} (l : List A)
    (H : ((l.length : Nat) : Int) < 2 ^ 64) : word_to_nat (len_word l) = l.length := by
  unfold word_to_nat
  have h := len_word_unsigned l H
  omega

/-- [fd32] on small values and on AT_FDCWD. -/
theorem fd32_small (fd : word) (H : (fd.toNat : Int) < 2 ^ 32) : fd32 fd = fd := by
  unfold fd32 abi_low32 LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32
  rw [Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fd.isLt]

theorem fd32_AT_FDCWD : fd32 AT_FDCWD = AT_FDCWD32 := rfl

/-- Any register value whose low 32 bits are those of -100 names AT_FDCWD. -/
theorem fd32_is_AT_FDCWD32 (w : word)
    (Hw : (w.toNat : Int) % 2 ^ 32 = 2 ^ 32 - 100) : fd32 w = AT_FDCWD32 := by
  have hA : AT_FDCWD32 = BitVec.ofNat 64 (2 ^ 32 - 100) := by decide
  have h1 : w.toNat % 2 ^ 32 = 2 ^ 32 - 100 := by omega
  unfold fd32 abi_low32 LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32
  rw [h1, hA]

theorem AT_FDCWD_low32 : (AT_FDCWD.toNat : Int) % 2 ^ 32 = 2 ^ 32 - 100 := by decide

/- =========================================================================
   PART 1 — generic checker-driven syscall nodes
   ========================================================================= -/

/-- Inversion of one [sstep] at a pending syscall whose spec never says
    [Unmodeled] and never halts: it is an [sstep_syscall]. -/
theorem sstep_sys_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (e : List event) (st : step_to)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hnu : ¬ syscall_spec (sys_input segs ms x8) model .unmodeled)
    (Hnh : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      syscall_spec (sys_input segs ms x8) model (.ok eff m' evs) → m_halted m' = none)
    (Hnl : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      syscall_spec (sys_input segs ms x8) model (.ok eff m' evs) → m_vm_lazy m' = [])
    (Hss : sstep segs (mkCfg ms model) e st) :
    ∃ (eff : SyscallEffect) (m' : Model),
      syscall_spec (sys_input segs ms x8) model (.ok eff m' e)
        ∧ st = .SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m') := by
  cases Hss with
  | instr _ _ ms' model' hh hsvc hstep => rw [Hsvc] at hsvc; simp at hsvc
  | instr_fault _ _ hh hsvc hstep => rw [Hsvc] at hsvc; simp at hsvc
  | instr_unmodeled _ _ hh hsvc hstep => rw [Hsvc] at hsvc; simp at hsvc
  | syscall _ _ x8' eff model' model'' _ hh hsvc hspec hh' hmat =>
      rw [Hsvc] at hsvc
      obtain rfl := Option.some.inj hsvc
      rw [materialize_model_accesses_no_lazy model' (syscall_effect_accesses eff)
        (Hnl eff model' e hspec)] at hmat
      obtain rfl := Option.some.inj hmat
      exact ⟨eff, model', hspec, rfl⟩
  | syscall_materialization_fault _ _ x8' eff model' evs hh hsvc hspec hh' hmat =>
      rw [Hsvc] at hsvc
      obtain rfl := Option.some.inj hsvc
      rw [materialize_model_accesses_no_lazy model' (syscall_effect_accesses eff)
        (Hnl eff model' evs hspec)] at hmat
      simp at hmat
  | exit _ _ x8' eff model' evs code hh hsvc hspec hh' hk =>
      rw [Hsvc] at hsvc
      obtain rfl := Option.some.inj hsvc
      exact absurd (Hnh eff model' evs hspec) (by rw [hh']; simp)
  | killed _ _ x8' eff model' evs sig hh hsvc hspec hk =>
      rw [Hsvc] at hsvc
      obtain rfl := Option.some.inj hsvc
      rw [m_killed_of_m_halted_none model' (Hnh eff model' evs hspec)] at hk
      simp at hk
  | syscall_unmodeled _ _ x8' hh hsvc hspec =>
      rw [Hsvc] at hsvc
      obtain rfl := Option.some.inj hsvc
      exact absurd hspec Hnu

/-- THE generic node: resolutions indexed by [I], characterized through
    [syscall_spec] directly. -/
theorem node_sys (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (I : Type) (E : I → SyscallEffect) (M : I → Model) (EV : I → List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hcomp : ∀ i, syscall_spec (sys_input segs ms x8) model (.ok (E i) (M i) (EV i)))
    (Hsound : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      syscall_spec (sys_input segs ms x8) model (.ok eff m' evs) →
        ∃ i, eff = E i ∧ m' = M i ∧ evs = EV i)
    (Hnu : ¬ syscall_spec (sys_input segs ms x8) model .unmodeled)
    (Hnh : ∀ i, m_halted (M i) = none) (Hnl : ∀ i, m_vm_lazy (M i) = []) :
    node_ok segs (mkCfg ms model) I EV
      (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) := by
  constructor
  · intro i
    exact .syscall ms model x8 (E i) (M i) (M i) (EV i) Hh Hsvc (Hcomp i) (Hnh i)
      (by rw [materialize_model_accesses_no_lazy (M i) (syscall_effect_accesses (E i))
        (Hnl i)])
  · intro e st Hss
    have Hnh' : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        syscall_spec (sys_input segs ms x8) model (.ok eff m' evs) → m_halted m' = none := by
      intro eff m' evs Hs
      obtain ⟨i, -, rfl, -⟩ := Hsound eff m' evs Hs
      exact Hnh i
    have Hnl' : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
        syscall_spec (sys_input segs ms x8) model (.ok eff m' evs) → m_vm_lazy m' = [] := by
      intro eff m' evs Hs
      obtain ⟨i, -, rfl, -⟩ := Hsound eff m' evs Hs
      exact Hnl i
    obtain ⟨eff, m', Hs, hst⟩ := sstep_sys_inv segs ms model x8 e st Hh Hsvc Hnu Hnh' Hnl' Hss
    obtain ⟨i, rfl, rfl, rfl⟩ := Hsound eff m' e Hs
    exact ⟨i, rfl, hst⟩

/-- The same node read off the verified executable checker.  [chk] is
    what [check_syscall] reduces to at this state (as a function of the
    candidate effect). -/
theorem node_sys_chk (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (chk : SyscallEffect → check_result) (I : Type)
    (E : I → SyscallEffect) (M : I → Model) (EV : I → List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model = chk eff)
    (Hok : ∀ i, chk (E i) = .CheckOk (M i) (EV i))
    (Hinv : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      chk eff = .CheckOk m' evs → ∃ i, eff = E i ∧ m' = M i ∧ evs = EV i)
    (Hnu : ∀ eff, chk eff ≠ .CheckUnmodeled)
    (Hnh : ∀ i, m_halted (M i) = none) (Hnl : ∀ i, m_vm_lazy (M i) = []) :
    node_ok segs (mkCfg ms model) I EV
      (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) := by
  refine node_sys segs ms model x8 I E M EV Hh Hsvc ?_ ?_ ?_ Hnh Hnl
  · intro i
    rw [← check_syscall_ok_iff, Hchk]
    exact Hok i
  · intro eff m' evs Hs
    rw [← check_syscall_ok_iff, Hchk] at Hs
    exact Hinv eff m' evs Hs
  · intro Hs
    exact Hnu (mkEffect (BitVec.ofInt 64 0) [] []) (by
      rw [← Hchk]
      exact (check_syscall_err_iff _ _ _).mpr Hs)

/-- Realization through an indexed node (general shape). -/
theorem rz_sys_chk (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (chk : SyscallEffect → check_result) (I : Type)
    (E : I → SyscallEffect) (M : I → Model) (EV : I → List event) (T : I → TSet) (i0 : I)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model = chk eff)
    (Hok : ∀ i, chk (E i) = .CheckOk (M i) (EV i))
    (Hinv : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      chk eff = .CheckOk m' evs → ∃ i, eff = E i ∧ m' = M i ∧ evs = EV i)
    (Hnu : ∀ eff, chk eff ≠ .CheckUnmodeled)
    (Hnh : ∀ i, m_halted (M i) = none) (Hnl : ∀ i, m_vm_lazy (M i) = [])
    (Hcont : ∀ i, realizes segs (mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) (T i)) :
    realizes segs (mkCfg ms model) (t_alt (fun i => t_emit (EV i) (T i))) := by
  refine .rz_node (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) T i0 ?_ ?_
  · exact node_sys_chk segs ms model x8 chk I E M EV Hh Hsvc Hchk Hok Hinv Hnu Hnh Hnl
  · exact Hcont

/-- Silent indexed node whose continuations all realize the SAME shape. -/
theorem rz_sys_chk_const (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (chk : SyscallEffect → check_result) (I : Type)
    (E : I → SyscallEffect) (M : I → Model) (T : TSet) (i0 : I)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model = chk eff)
    (Hok : ∀ i, chk (E i) = .CheckOk (M i) [])
    (Hinv : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      chk eff = .CheckOk m' evs → ∃ i, eff = E i ∧ m' = M i ∧ evs = [])
    (Hnu : ∀ eff, chk eff ≠ .CheckUnmodeled)
    (Hnh : ∀ i, m_halted (M i) = none) (Hnl : ∀ i, m_vm_lazy (M i) = [])
    (Hcont : ∀ i, realizes segs (mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) T) :
    realizes segs (mkCfg ms model) T := by
  refine .rz_conseq (mkCfg ms model) (t_alt (fun _ : I => t_emit [] T)) T ?_ ?_
  · exact rz_sys_chk segs ms model x8 chk I E M (fun _ => []) (fun _ => T) i0
      Hh Hsvc Hchk Hok Hinv Hnu Hnh Hnl Hcont
  · have HT : T [] := realizes_nonempty segs _ T (Hcont i0)
    intro tr
    constructor
    · rintro ⟨i, Hi⟩
      exact (t_emit_nil_eq T HT tr).1 Hi
    · intro Htr
      exact ⟨i0, (t_emit_nil_eq T HT tr).2 Htr⟩

/-- Deterministic ret-only node: the checker is [check_ret_only eff r m' evs]. -/
theorem rz_ret_chk (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (r : word) (m' : Model) (evs : List event) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = check_ret_only eff r m' evs)
    (Hh' : m_halted m' = none) (Hnl' : m_vm_lazy m' = [])
    (Hcont : realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') T) :
    realizes segs (mkCfg ms model) (t_emit evs T) := by
  refine .rz_conseq (mkCfg ms model) (t_alt (fun _ : Unit => t_emit evs T))
    (t_emit evs T) ?_ (t_alt_unit _)
  refine rz_sys_chk segs ms model x8 (fun eff => check_ret_only eff r m' evs) Unit
    (fun _ => mkEffect r [] []) (fun _ => m') (fun _ => evs) (fun _ => T) ()
    Hh Hsvc Hchk ?_ ?_ ?_ (fun _ => Hh') (fun _ => Hnl') (fun _ => Hcont)
  · intro i
    cases i
    exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩
  · intro eff m2 evs2 Hc
    obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp Hc
    exact ⟨(), heff, hm, hevs⟩
  · intro eff
    exact check_ret_only_no_unmodeled eff r m' evs

/-- ... and its silent special case. -/
theorem rz_ret_chk_silent (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (r : word) (m' : Model) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = check_ret_only eff r m' [])
    (Hh' : m_halted m' = none) (Hnl' : m_vm_lazy m' = [])
    (Hcont : realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect r [] []))) m') T) :
    realizes segs (mkCfg ms model) T := by
  refine .rz_conseq (mkCfg ms model) (t_emit [] T) T ?_ ?_
  · exact rz_ret_chk segs ms model x8 r m' [] T Hh Hsvc Hchk Hh' Hnl' Hcont
  · exact t_emit_nil_eq T (realizes_nonempty segs _ T Hcont)

/- =========================================================================
   PART 2 — the [ecall] instruction step and post-syscall state collapse
   ========================================================================= -/

/-- More argument-register index facts (a3..a5), cf. [PropExec.arg_reg_0]. -/
theorem arg_reg_3 : BitVec.ofInt 5 (10 + (3 : Int)) = (13 : reg) := by decide

theorem arg_reg_4 : BitVec.ofInt 5 (10 + (4 : Int)) = (14 : reg) := by decide

theorem arg_reg_5 : BitVec.ofInt 5 (10 + (5 : Int)) = (15 : reg) := by decide

section EcallState

variable [fx : PropExec.FPState]

/- that `variable` is  `Context {fx : FPState}`.  The
   harness lemmas this section consumes ([PropExec.step_ecall],
   [FileSim.adv_eff_ret], ...) carry an `[FPState]` parameter their statements
   do not mention, so the section is generic in it and every use site inside
   picks up the same instance. -/

/-- The machine state right after the [ecall] INSTRUCTION executed at
    [mkst regs pc mem rom]: only [ms_svc_pending] changed (:= a7). -/
def ecall_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
    ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
    ms_mem := mem, ms_rom := rom }

theorem step_ecall_st (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineOk (ecall_st regs pc mem rom) := by
  rw [PropExec.step_ecall segs regs pc mem rom w Hfetch Hecall]
  rfl

theorem ecall_st_svc (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_svc_pending (ecall_st regs pc mem rom) = some (getr regs 17) := rfl

theorem ecall_st_mem (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_mem (ecall_st regs pc mem rom) = mem := rfl

theorem ecall_st_rom (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_rom (ecall_st regs pc mem rom) = rom := rfl

theorem ecall_st_pc (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_pc (ecall_st regs pc mem rom) = pc := rfl

theorem ecall_st_gpr0 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (ecall_st regs pc mem rom) 0 = getr regs 10 := by
  have hreg : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
  have h : ms_gpr (ecall_st regs pc mem rom) 0 = reg_get regs (10 : reg) := by
    simp only [ecall_st, ms_gpr, hreg]
  rw [h]
  exact (getr_nz regs (10 : reg) (by decide)).symm

theorem ecall_st_gpr1 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (ecall_st regs pc mem rom) 1 = getr regs 11 := by
  have hreg : BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide
  have h : ms_gpr (ecall_st regs pc mem rom) 1 = reg_get regs (11 : reg) := by
    simp only [ecall_st, ms_gpr, hreg]
  rw [h]
  exact (getr_nz regs (11 : reg) (by decide)).symm

theorem ecall_st_gpr2 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (ecall_st regs pc mem rom) 2 = getr regs 12 := by
  have hreg : BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) := by decide
  have h : ms_gpr (ecall_st regs pc mem rom) 2 = reg_get regs (12 : reg) := by
    simp only [ecall_st, ms_gpr, hreg]
  rw [h]
  exact (getr_nz regs (12 : reg) (by decide)).symm

theorem ecall_st_gpr3 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (ecall_st regs pc mem rom) 3 = getr regs 13 := by
  have hreg : BitVec.ofInt 5 (10 + ((3 : Nat) : Int)) = (13 : reg) := by decide
  have h : ms_gpr (ecall_st regs pc mem rom) 3 = reg_get regs (13 : reg) := by
    simp only [ecall_st, ms_gpr, hreg]
  rw [h]
  exact (getr_nz regs (13 : reg) (by decide)).symm

theorem ecall_st_gpr4 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (ecall_st regs pc mem rom) 4 = getr regs 14 := by
  have hreg : BitVec.ofInt 5 (10 + ((4 : Nat) : Int)) = (14 : reg) := by decide
  have h : ms_gpr (ecall_st regs pc mem rom) 4 = reg_get regs (14 : reg) := by
    simp only [ecall_st, ms_gpr, hreg]
  rw [h]
  exact (getr_nz regs (14 : reg) (by decide)).symm

theorem ecall_st_gpr5 (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_gpr (ecall_st regs pc mem rom) 5 = getr regs 15 := by
  have hreg : BitVec.ofInt 5 (10 + ((5 : Nat) : Int)) = (15 : reg) := by decide
  have h : ms_gpr (ecall_st regs pc mem rom) 5 = reg_get regs (15 : reg) := by
    simp only [ecall_st, ms_gpr, hreg]
  rw [h]
  exact (getr_nz regs (15 : reg) (by decide)).symm

/-- Memory views of the ecall state. -/
theorem ecall_st_read_byte (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) :
    ms_read_byte (ecall_st regs pc mem (seg_rom segs)) = mrb segs mem := rfl

theorem ecall_st_read_bytes (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (a n : word) :
    ms_read_bytes (ecall_st regs pc mem (seg_rom segs)) a n
      = rdn segs mem a (word_to_nat n) :=
  ms_read_bytes_rdn segs _ a n rfl

theorem ecall_st_writable (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) :
    ms_writable_byte segs (ecall_st regs pc mem rom) = wview segs mem := rfl

/-- Post-syscall state collapse lemmas. -/
theorem adv_ret_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte) (r : word) :
    advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffect r [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom := by
  unfold ecall_st
  exact adv_eff_ret regs pc (getr regs 17) mem rom r

theorem adv_setgpr0_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (r : word) :
    advance_past_svc (set_gpr0 (ecall_st regs pc mem rom) r)
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom := by
  unfold ecall_st
  exact adv_set regs pc (some (getr regs 17)) mem rom r

theorem adv_write_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (r buf : word) (data : List byte) :
    advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffect r [(buf, data)] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  unfold ecall_st
  exact adv_apply_write regs pc (some (getr regs 17)) mem rom r buf data

theorem adv_delivered_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (r buf : word) (data : List byte) :
    advance_past_svc (apply_effect (ecall_st regs pc mem rom)
        (mkEffect r (delivered_writes buf data) []))
      = mkst (regupd regs 10 r) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  unfold ecall_st
  exact adv_apply_delivered regs pc (some (getr regs 17)) mem rom r buf data

theorem adv_grant_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (a n : word) :
    advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffect a [] [(a, n)]))
      = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom := by
  unfold ecall_st
  exact adv_mmap_grant regs pc (some (getr regs 17)) mem rom a n

/-- [write_to_mem] is [CatExec.wbytes] (same recursion, definitionally). -/
theorem write_to_mem_wbytes (data : List byte) (mem : word → Option byte) (a : word) :
    write_to_mem mem a data = wbytes mem a data :=
  CatExec.write_to_mem_wbytes data mem a

/-- The instruction step INTO the pending-syscall state, as a [realizes]
    rule. -/
theorem rz_ecall (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfetch : fetch_word segs pc = some w) (He : is_ecall w = true)
    (Hc : realizes segs (mkCfg (ecall_st regs pc mem rom) model) T) :
    realizes segs (mkCfg (mkst regs pc mem rom) model) T :=
  rz_step segs (mkst regs pc mem rom) model (ecall_st regs pc mem rom) T Hh Hlazy rfl
    (step_ecall_st segs regs pc mem rom w Hfetch He) Hc

end EcallState

end LinuxSem.Common.ShapeNodes
