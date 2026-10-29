/-
  * Common.MmapSim — reusable trace-semantics infrastructure for binaries
    that perform ONE anonymous mmap whose two resolutions (any-errno
    failure / nondeterministically-placed zero-filled grant) lead to two
    deterministic tails: a "failure" tail (writes [bf], exits [cf]) and a
    "success" tail (writes [bs], exits [cs], possibly munmapping the grant
    on the way).

  TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.CatSim).
  Generic over the loaded segments [segs].

  Buffers are [List byte] with [byte = BitVec 8]; addresses, lengths,
  errnos-as-returns and exit codes are [word = BitVec 64].  Following the
  ExitSim/CatSim/AllocSim conventions:

  - every syscall-number test is Int-characterized: the pending number
    [x8] satisfies [(x8.toNat : Int) = 64/215/222] (write / munmap /
    mmap) instead of pinning a [BitVec] literal spelling;
  - all no-wrap bookkeeping (page rounding, the allocation-ceiling
    bound, interval disjointness, error-range checks) is in [Int] over
    [toNat]: [grant_ok] takes the ROUNDED length as an [Int]
    ([page_round_up_Z (len.toNat : Int)]), and only the stored length
    re-enters [word] via the local [page_round_up : word → word]
    (= [BitVec.ofInt 64] of the [Int] round-up, matching
    [Mmap.mmap_spec]);
  - exit codes are masked with [&&& BitVec.ofInt 64 255]; machine
    records carry the new [ms_resv := none] field; post-ecall pcs are
    [v_addi pc 4].

  Structure:

  - [twm]: to_wexit extended with a [munmap] rule (for the MODELED
    munmap shape — page-aligned addr, nonzero len, page-rounding
    exactly a recorded mapping ([munmap_args_ok]) — munmap has a
    UNIQUE outcome: return 0, drop the mapping, unmap the range, no
    events) and threading the model state (munmap changes [vm_maps]
    but preserves the fd table, the file system and haltedness).
  - [tmw]: a deterministic prefix of instruction steps reaching an mmap
    ecall of the ONE modeled register shape ([mmap_args_ok]), whose
    two families of resolutions each land in a [twm] derivation — the
    SAME [(bf, cf)] for every errno in [mmap_errnos], the SAME
    [(bs, cs)] for every admissible grant address — plus a witness that
    at least one admissible grant address exists.
  - The omni reading: [twm_exec_mut] and [tmw_exec] are ONE judgment
    each ([OmniRun.exec]), from which the trace characterization — the
    observable prefix set of such a run is exactly the prefixes of the
    two candidate traces ([wevents bf ++ ExitEv cf] and
    [wevents bs ++ ExitEv cs]) — and the absence of the explicit error
    transition both follow.
  - [mmap_strong_equiv_te]: two such binaries with the same [(bf, cf)]
    and [(bs, cs)] are observably equivalent; [mmap_omni_strong_equiv_te]
    is the same in the shape of [OmniEquivalence.omni_strong_equiv].

  Also: generic per-instruction step lemmas the mmap examples need
  beyond Common.PropExec/SeqExec (byte stores of arbitrary byte
  values), the [zfill] memory overlay a successful grant produces, the
  [unfill] overlay a munmap leaves behind (the unmapped range reads as
  UNMAPPED, so a later access faults; [Run.apply_effect] uses the same
  [eff_unmaps] ledger for a moved or shrinking mremap), and arithmetic
  helpers ([wbytes_snoc], [v_srli_div], [grant_ok] unpacking).

  NOTES.

  - `Section WithFP1`'s `Context {fx : FPState}` becomes the ambient
    `variable [fx : FPState]` of the same name, exactly as `PropExec`
    does it.
Combined Scheme twm_mutind` has no Lean
    counterpart to *define*: Lean's mutual-inductive block generates
    `twm.rec` with one motive per member, which is the same combined
    eliminator.  [twm_exec_mut] below consumes it in the same shape.
  - `lia` is `omega`; `vm_compute; reflexivity` is `decide`;
    `Z_to_bv 64 z` is `BitVec.ofInt 64 z`; `bv_and` is `&&&`;
    `bv_unsigned w` is `(w.toNat : Int)`.
  The whole file is present: every definition and every
  lemma of the, including the mutual [twm] induction, the
  [tmw] branching node, the omni-exec readings ([twm_exec_mut],
  [twm_exec], [tmw_exec]) and the two equivalence packagings
  ([mmap_omni_strong_equiv_te], [mmap_strong_equiv_te]).
  Nothing is deferred: the last two, [step_sb_any] and [step_sb_at] (the
  byte-store step lemmas of the "extra per-instruction step lemmas"
  section), are proved on top of [Common.SeqExec]'s [step_sb] — the [SZ1]
  twin of `Common.CatExec`'s `step_sd` — plus
  [SeqExec.N_to_le_bytes_1_small]; [step_sb_at] is [step_sb_any] with the
  address / word / byte pre-normalized.
  DEPENDENCIES.  [Common.SeqExec] is imported for [step_sb] and
  [N_to_le_bytes_1_small] (and brings [Common.CatExec] in, whose
  `CatExec.wbytes` is the [wbytes] [step_sb] concludes over — the
  file-local INLINED [wbytes] is the same store walk, and on the singleton
  byte list of an [Sb] both reduce to the same one-byte update).
  [Common.CatSim] is imported for the write-syscall facts
  the [twm_pend] rule needs ([write1_ok_n], [write1_ok_inv],
  [sstep_write_inv], [sstep_write_next_inv]), for [fd1chan],
  [buf_modeled]/[bufs_modeled] (+ [buf_modeled_skipn]) and for
  [wevents], [msteps] and [init_model_fd1chan].  [Common.AllocSim]'s
  [zmem] is still unwired, and the INLINED [wbytes]/[zmem] block is left
  in place (every local proof is stated over it — switching it to
  `CatExec.wbytes` is a separate cleanup), so those
  (with [wbytes_snoc], [zmem_out], [zfill], [zfill_out]) stay carried
  here, marked `INLINED FROM`; delete the marked block when the modules
  land.  [adv_set] and [land_255_small] are the same story (CatExec /
  BvBase).
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
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Mm.Mmap
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.MmapSim

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
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Prelude (errno_ret_in errno_ret_in_below errno_ret_in_true
  errno_ret_in_intro errnos_ok errnos_ok_range listNN_eqb listNN_eqb_eq check_result)
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim (apply_effect_no_write apply_effect_copyins_no_write
  init_model_fd1chan fd1chan wevents msteps
  buf_modeled bufs_modeled bufs_modeled_single
  buf_modeled_nil buf_modeled_skipn write1_ok_n write1_ok_inv write1_no_unmodeled
  sstep_write_inv sstep_write_next_inv)
open LinuxSem.Common.CatSim (apply_effect_no_write apply_effect_copyins_no_write
  init_model_fd1chan fd1chan wevents msteps
  buf_modeled bufs_modeled bufs_modeled_single
  buf_modeled_nil buf_modeled_skipn write1_ok_n write1_ok_inv write1_no_unmodeled
  sstep_write_inv sstep_write_next_inv)
open LinuxSem.Common.CatExec

variable [fx : FPState]

/- =========================================================================
   Extra per-instruction step lemmas
   ========================================================================= -/

/- v_srli/step_srli live in PropExec (identical shapes). -/

/-- Unsigned-shift-right is division, at the [toNat] level (the old
    [x < 2^64] hypothesis is typed away; the guard stays [Int]). -/
theorem v_srli_div (x : word) (sh : Int) (Hsh : 0 ≤ sh ∧ sh < 64) :
    ((v_srli x sh).toNat : Int) = (x.toNat : Int) / ((2 ^ sh.toNat : Nat) : Int) := by
  simp only [v_srli, zshiftr, toNat_ofInt_64, natCast_emod64_toNat]
  have hpos : (0 : Int) < ((2 ^ sh.toNat : Nat) : Int) := by
    rw [Int.natCast_pow]
    exact Int.pow_pos (by decide)
  have hx := u64_range x
  have hz0 : 0 ≤ (x.toNat : Int) / ((2 ^ sh.toNat : Nat) : Int) :=
    Int.ediv_nonneg hx.1 (Int.le_of_lt hpos)
  have hzle : (x.toNat : Int) / ((2 ^ sh.toNat : Nat) : Int) ≤ (x.toNat : Int) :=
    Int.ediv_le_self _ hx.1
  have hlt : (x.toNat : Int) / ((2 ^ sh.toNat : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by
    omega
  exact Int.emod_eq_of_lt hz0 hlt

/- =========================================================================
   INLINED FROM Common.CatExec: wbytes

   [wbytes] is the memory-level mirror of the interpreter's store path
   (CatExec's `wbytes`); it is carried here as the same store walk under a
   file-local name, which every proof in this file is stated over.
   [Common.CatExec] is now in the tree (via [Common.SeqExec]), so a future
   cleanup can alias this to `CatExec.wbytes`; until then the two are
   related on the singleton list of an [Sb] by the closing proofs of
   [step_sb_any]/[step_sb_at].
   ========================================================================= -/

/-- Apply a byte list one byte at a time, starting at [addr] (CatExec's
    store walk). -/
def wbytes (m : word → Option byte) (addr : word) (bs : List byte) :
    word → Option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then some b else m a) (addr + 1) rest

/- =========================================================================
   wbytes: append a byte at the end of an accumulated store run
   ========================================================================= -/

theorem wbytes_snoc (bs : List byte) (m : word → Option byte) (a : word) (b : byte) :
    wbytes m a (bs ++ [b]) =
      wbytes (wbytes m a bs) (a + nat_to_word bs.length) [b] := by
  induction bs generalizing m a with
  | nil =>
    simp only [List.nil_append, wbytes, List.length_nil]
    /- `simp only`, not `rw`: the occurrence sits inside the `ite`'s
       `Decidable` argument, so `rw`'s motive is `fun _a => if bv_eqb a_1
       _a = true then …`, which is not type correct — rewriting the term
       under a decidable instance is what `simp` does and `rw` refuses. -/
    simp only [word_add_0]
  | cons x r ih =>
    simp only [List.cons_append, wbytes, List.length_cons]
    rw [ih, word1_nat, nat_to_word_add_merge, Nat.add_comm 1 r.length]
    rfl

/- =========================================================================
   The zero-filled grant overlay
   ========================================================================= -/

/-- INLINED FROM Common.AllocSim: the zero-fill of a single granted range
    [b, b+l).  Coverage is checked in [Int] over unsigned values,
    mirroring [Run.zeros_cover] (grant ranges never wrap). -/
def zmem (mem : word → Option byte) (b l : word) : word → Option byte :=
  fun a =>
    if decide ((b.toNat : Int) ≤ (a.toNat : Int)) &&
       decide ((a.toNat : Int) < (b.toNat : Int) + (l.toNat : Int))
    then some (BitVec.ofInt 8 0) else mem a

/-- The zero-filled grant overlay is the SAME operation as
    [AllocSim.zmem] up to argument order ([zfill a n m = zmem m a n]);
    it is kept here as a thin alias so mmap-side proofs read naturally
    ([zfill addr len mem]).  Coverage is checked in [Int] over unsigned
    values, mirroring [Run.zeros_cover] (grant ranges never wrap). -/
def zfill (a n : word) (m : word → Option byte) : word → Option byte :=
  zmem m a n

/-- INLINED FROM Common.AllocSim: a read outside the zeroed range is
    unchanged. -/
theorem zmem_out (mem : word → Option byte) (b l : word) (a : word)
    (Hd : (a.toNat : Int) < (b.toNat : Int) ∨
          (b.toNat : Int) + (l.toNat : Int) ≤ (a.toNat : Int)) :
    zmem mem b l a = mem a := by
  unfold zmem
  rcases Hd with Hd | Hd
  · have E : decide ((b.toNat : Int) ≤ (a.toNat : Int)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [E]
    rfl
  · have E : decide ((a.toNat : Int) < (b.toNat : Int) + (l.toNat : Int)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [E, Bool.and_false]
    rfl

theorem zfill_out (a n : word) (m : word → Option byte) (x : word)
    (Hx : (x.toNat : Int) < (a.toNat : Int) ∨
          (a.toNat : Int) + (n.toNat : Int) ≤ (x.toNat : Int)) :
    zfill a n m x = m x :=
  zmem_out m a n x Hx

/-- NEW no-overflow hypothesis (inherited from the Bv [rdn_ext]); trivial
    at call sites — the read window sits far below 2^64. -/
theorem rdn_zfill_out (segs : List Segment) (a n : word) (m : word → Option byte)
    (x : word) (k : Nat)
    (Hnw : (x.toNat : Int) + (k : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hd : (x.toNat : Int) + (k : Int) ≤ (a.toNat : Int) ∨
          (a.toNat : Int) + (n.toNat : Int) ≤ (x.toNat : Int)) :
    rdn segs (zfill a n m) x k = rdn segs m x k := by
  apply rdn_ext segs k
  · exact Hnw
  · intro y Hy
    apply zfill_out
    omega

/- =========================================================================
   Model transformers for mmap / munmap
   ========================================================================= -/

def munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n
    (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
      (map_remove (m_vmmaps m).vm_maps addr)
      (maps_subtract (m_vmmaps m).vm_noaccess
        (addr.toNat : Int)
        ((addr.toNat : Int) + (n.toNat : Int)))
      (m_vmmaps m).vm_start_brk
      (m_vmmaps m).vm_brk
      (m_vmmaps m).vm_limit
      (m_vmmaps m).vm_mmap_base
      (m_vmmaps m).vm_init_sp) m

def mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
    ((a, n) :: (m_vmmaps m).vm_maps)
    (m_vmmaps m).vm_noaccess
    (m_vmmaps m).vm_start_brk
    (m_vmmaps m).vm_brk
    (m_vmmaps m).vm_limit
    (m_vmmaps m).vm_mmap_base
    (m_vmmaps m).vm_init_sp) m

/-- The rounded grant length as a [word] — the value that lands in the
    effect's zero list and the model's [vm_maps] entry.  The bound
    checks always use the un-wrapped [Int] round-up
    [page_round_up_Z (len.toNat : Int)] (a length within a page of 2^64
    must FAIL the ceiling check, not wrap to a small number). -/
def page_round_up (len : word) : word :=
  BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))

/-- May the kernel grant [a, a+n)?  [n] is the ROUNDED length in [Int]
    and [hint] is the caller's addr argument (a0); matches
    [Mmap.mmap_spec]'s choose / [check_mmap]'s condition, including the
    allocation-budget conjunct ([State.vm_limit]).

    [hint] IS DEAD: the spec constrains a preference-free placement by
    admissibility alone, so a NULL hint and a free non-NULL one accept
    the same addresses. -/
def grant_ok (hint : word) (m : Model) (a : word) (n : Int) : Bool :=
  decide ((a.toNat : Int) % page_size = 0) && decide (0 < (a.toNat : Int))
  && decide ((a.toNat : Int) + n ≤ alloc_top (m_vmmaps m))
  && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
       (BitVec.ofInt 64 n)
  && decide (vm_backing_used m + n ≤ (m_vmmaps m).vm_limit)

theorem munmap_model_halted (addr n : word) (m : Model) :
    m_halted (munmap_model addr n m) = m_halted m := by
  simp only [munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing,
    with_vmmaps, m_halted]

theorem munmap_model_fs (addr n : word) (m : Model) :
    m_fs (munmap_model addr n m) = m_fs m := by
  simp only [munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing,
    with_vmmaps, m_fs]

theorem munmap_model_fd1chan (addr n : word) (m : Model) (H : fd1chan m) :
    fd1chan (munmap_model addr n m) := by
  unfold fd1chan at *
  simpa only [munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing,
    with_vmmaps, m_fds] using H

theorem munmap_model_no_lazy (addr n : word) (m : Model)
    (Hlazy : m_vm_lazy m = []) : m_vm_lazy (munmap_model addr n m) = [] := by
  simp only [munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing,
    with_vmmaps, m_vm_lazy]
  rw [show m.m_vm.vmst_lazy = [] from Hlazy]
  rfl

theorem mmap_model_halted (a n : word) (m : Model) :
    m_halted (mmap_model a n m) = m_halted m := by
  simp only [mmap_model, with_vmmaps, m_halted]

theorem mmap_model_fs (a n : word) (m : Model) :
    m_fs (mmap_model a n m) = m_fs m := by
  simp only [mmap_model, with_vmmaps, m_fs]

theorem mmap_model_fd1chan (a n : word) (m : Model) (H : fd1chan m) :
    fd1chan (mmap_model a n m) := by
  unfold fd1chan at *
  simpa only [mmap_model, with_vmmaps, m_fds] using H

theorem mmap_model_lazy (a n : word) (m : Model) :
    m_vm_lazy (mmap_model a n m) = m_vm_lazy m := by
  simp only [mmap_model, with_vmmaps, m_vm_lazy]

/-- Unpack [grant_ok] ([Int]-level facts now). -/
theorem grant_ok_unpack (hint : word) (m : Model) (a : word) (n : Int)
    (H : grant_ok hint m a n = true) :
    (a.toNat : Int) % page_size = 0 ∧ 0 < (a.toNat : Int) ∧
    (a.toNat : Int) + n ≤ alloc_top (m_vmmaps m) ∧
    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
      (BitVec.ofInt 64 n) = true ∧
    vm_backing_used m + n ≤ (m_vmmaps m).vm_limit := by
  unfold grant_ok at H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  exact ⟨H.1.1.1.1, H.1.1.1.2, H.1.1.2, H.1.2, H.2⟩

theorem region_free_cons (b s : word) (r : List (word × word)) (lo n : word)
    (H : region_free ((b, s) :: r) lo n = true) :
    ((lo.toNat : Int) + (n.toNat : Int) ≤ (b.toNat : Int) ∨
      (b.toNat : Int) + (s.toNat : Int) ≤ (lo.toNat : Int)) ∧
    region_free r lo n = true := by
  simp only [region_free, Bool.and_eq_true] at H
  obtain ⟨H1, H2⟩ := H
  refine ⟨?_, H2⟩
  have hiv : iv_overlap lo n b s = false := by simpa using H1
  unfold iv_overlap at hiv
  rw [Bool.and_eq_false_iff] at hiv
  rcases hiv with h | h
  · have h' : ¬ ((lo.toNat : Int) < (b.toNat : Int) + (s.toNat : Int)) := by simpa using h
    omega
  · have h' : ¬ ((b.toNat : Int) < (lo.toNat : Int) + (n.toNat : Int)) := by simpa using h
    omega

/-- Numeric restatements of the per-role allocation budgets
    ([State.source_alloc_limit]/[State.target_alloc_limit]) — [omega]
    treats the constants as opaque atoms, so proofs consuming budget
    bounds rewrite these first. -/
theorem source_alloc_limit_val : source_alloc_limit = 0x400000000 := rfl

theorem target_alloc_limit_val : target_alloc_limit = 0x8000000000 := rfl

/- =========================================================================
   Syscall-input decode facts
   ========================================================================= -/

/- in_sysno_sys_input lives in ExitSim; in_arg1_sys_input in StreamSim. -/

theorem in_arg3_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3 := rfl

theorem in_arg4_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4 := rfl

theorem in_arg5_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5 := rfl

/- =========================================================================
   munmap: the modeled register/ledger shape
   ========================================================================= -/

/-- The register shape of the ONE mmap call the model covers (see
    [Mmap.mmap_modeled_b]): len (a1) nonzero, prot (a2) =
    PROT_READ|PROT_WRITE, flags (a3) = MAP_PRIVATE|MAP_ANONYMOUS,
    offset (a5) = 0.  a0 — the placement hint — is unconstrained
    (without MAP_FIXED the kernel is free to ignore it), and so is
    fd (a4), which the shape does not read; the conjunct pinning it to
    -1 stays because it is the register state a musl grant really
    presents. -/
def mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 ≠ BitVec.ofInt 64 0 ∧ ms_gpr ms 2 = BitVec.ofInt 64 3 ∧
  ms_gpr ms 3 = BitVec.ofInt 64 34 ∧ ms_gpr ms 4 = BitVec.ofInt 64 (-1) ∧
  ms_gpr ms 5 = BitVec.ofInt 64 0

/-- Under [mmap_args_ok] the two fail-closed gates of [check_mmap] /
    [mmap_spec] are open. -/
theorem mmap_args_ok_gates (ms : machine_state) (H : mmap_args_ok ms) :
    mmap_off_aligned_b (ms_gpr ms 5) = true ∧
    mmap_anon_b (ms_gpr ms 3) = true ∧
    w_is0 (ms_gpr ms 1) = false ∧
    mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true := by
  obtain ⟨H1, H2, H3, H4, H5⟩ := H
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mmap_off_aligned_b
    rw [H5]
    decide
  · unfold mmap_anon_b
    rw [H3]
    decide
  · unfold w_is0
    exact bv_eqb_neq _ _ H1
  · unfold mmap_modeled_b
    rw [H2, H3, H5]
    decide

/-- The munmap register/ledger shape whose outcome is unique: a
    page-aligned addr (a0) and nonzero len (a1) whose page-rounding
    exactly matches a recorded mapping — the shape a well-behaved
    program that munmaps exactly what it mmapped produces.  The range
    conjunct bounds the SUM [addr + n] by [State.TASK_SIZE], matching
    [Mmap.munmap_spec]'s gate: Linux answers -EINVAL past it before it
    looks at any mapping, and every grant the model makes sits far
    below it. -/
def munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  ((ms_gpr ms 0).toNat : Int) % page_size = 0 ∧
  ms_gpr ms 1 ≠ BitVec.ofInt 64 0 ∧
  ((ms_gpr ms 0).toNat : Int) + page_round_up_Z ((ms_gpr ms 1).toNat : Int) ≤ TASK_SIZE ∧
  map_has (m_vmmaps model).vm_maps (ms_gpr ms 0)
    (page_round_up (ms_gpr ms 1)) = true

/-- The unique admissible munmap effect: return 0 and unmap the range. -/
def munmap_eff (ms : machine_state) : SyscallEffect :=
  SyscallEffect.mkEffectU (BitVec.ofInt 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] []
    []

/- =========================================================================
   Which arm answers a syscall number, on the SPEC side
   ========================================================================= -/

/-- The spec table's arm for 215 (munmap), read off `spec_table`. -/
theorem lookup_arm_215 :
    lookup_arm spec_table (215 : Int) = some (arm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1))) := by
  simp [lookup_arm, spec_table, arm]

/-- The spec table's arm for 222 (mmap), read off `spec_table`. -/
theorem lookup_arm_222 :
    lookup_arm spec_table (222 : Int) =
      some (arm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
        (in_arg i 5))) := by
  simp [lookup_arm, spec_table, arm]

/-- Which arm answers this number, on the SPEC side.  [syscall_spec] is
    [dispatch spec_table], so fixing the number settles the table lookup by
    conversion and the dispatcher disappears.  This is the same one-line
    argument [Checks.Sys.DispatchCompute] makes for [check_syscall], made
    here instead: stating it against the spec rather than the checker is
    what lets this file import the mmap checker alone rather than the
    module that re-exports every arm's. -/
theorem syscall_spec_munmap (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : Outcome SyscallEffect Model event) (Hno : (x8.toNat : Int) = 215) :
    (Specs.syscall_spec (sys_input segs ms x8) model o ↔
      munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o) := by
  unfold Specs.syscall_spec Sys.Dispatch.dispatch
  rw [in_sysno_sys_input, Hno, lookup_arm_215]
  rfl

/-- The mmap half of [syscall_spec_munmap], same argument. -/
theorem syscall_spec_mmap (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : Outcome SyscallEffect Model event) (Hno : (x8.toNat : Int) = 222) :
    (Specs.syscall_spec (sys_input segs ms x8) model o ↔
      mmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5)
        (sys_input segs ms x8) model o) := by
  unfold Specs.syscall_spec Sys.Dispatch.dispatch
  rw [in_sysno_sys_input, Hno, lookup_arm_222]
  rfl

/- =========================================================================
   munmap: the unique admissible outcome (for the modeled shape)
   ========================================================================= -/

/-- Under [munmap_args_ok] the checker collapses to the single
    accepted effect. -/
theorem munmap_check_modeled (ms : machine_state) (model : Model) (eff : SyscallEffect)
    (Ha : munmap_args_ok ms model) :
    check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
    = (match eff with
       | ⟨r, [], [], us, [], []⟩ =>
           if w_is0 r && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
           then .CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
           else .CheckReject
       | _ => .CheckReject) := by
  obtain ⟨Hal, Hlen, Hnw, Hhas⟩ := Ha
  unfold check_munmap
  have hw : w_is0 (ms_gpr ms 1) = false := by
    unfold w_is0
    exact bv_eqb_neq _ _ Hlen
  have hz : (((ms_gpr ms 0).toNat : Int) % page_size == 0) = true := by
    rw [Hal]
    rfl
  have h1 : ¬ ((!(((ms_gpr ms 0).toNat : Int) % page_size == 0) || w_is0 (ms_gpr ms 1)) = true) := by
    rw [hz, hw]
    simp
  have h2 : ¬ (TASK_SIZE < ((ms_gpr ms 0).toNat : Int) +
      page_round_up_Z ((ms_gpr ms 1).toNat : Int)) := by omega
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [page_round_up] at Hhas ⊢
  rw [ite_eq_left Hhas]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases cs <;> cases ci <;> simp only [munmap_model]
    <;> rfl

/-- Under [munmap_args_ok] the munmap spec has exactly the one accepted
    outcome. -/
theorem munmap_ok (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : (x8.toNat : Int) = 215) (Ha : munmap_args_ok ms model) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []) := by
  apply (syscall_spec_munmap segs ms x8 model _ Hno).mpr
  apply check_munmap_sound_ok
  rw [munmap_check_modeled ms model (munmap_eff ms) Ha]
  simp only [munmap_eff]
  have hw : w_is0 (BitVec.ofInt 64 0) = true := by
    unfold w_is0
    exact LinuxSem.Common.PropExec.bv_eqb_refl _
  have hl : listNN_eqb [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
      [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] = true := (listNN_eqb_eq _ _).mpr rfl
  rw [hw, hl]
  simp


theorem munmap_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : (x8.toNat : Int) = 215) (Ha : munmap_args_ok ms model)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)) :
    eff = munmap_eff ms ∧
      model' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model ∧ evs = [] := by
  have H2 := (syscall_spec_munmap segs ms x8 model _ Hno).mp Hspec
  have H3 := check_munmap_complete_ok (ms_gpr ms 0) (ms_gpr ms 1) eff model model' evs
    (sys_input segs ms x8) H2
  rw [munmap_check_modeled ms model eff Ha] at H3
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws with
  | nil =>
    cases zs with
    | nil =>
      cases cs with
      | nil =>
        cases ci with
        | nil =>
          simp only [] at H3
          by_cases hc : (w_is0 r && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]) = true
          · rw [ite_eq_left hc] at H3
            obtain ⟨hm, he⟩ := check_result.CheckOk.inj H3
            simp only [Bool.and_eq_true] at hc
            obtain ⟨hr, hus⟩ := hc
            unfold w_is0 at hr
            have hrz : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq _ _).mp hr
            have hus' : us = [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] :=
              (listNN_eqb_eq _ _).mp hus
            subst hrz
            subst hus'
            refine ⟨?_, hm.symm, he.symm⟩
            simp only [munmap_eff]
          · rw [ite_eq_right hc] at H3
            exact absurd H3 (by simp)
        | cons _ _ => exact absurd H3 (by simp)
      | cons _ _ => exact absurd H3 (by simp)
    | cons _ _ => exact absurd H3 (by simp)
  | cons _ _ => exact absurd H3 (by simp)

theorem munmap_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : (x8.toNat : Int) = 215) (Ha : munmap_args_ok ms model) :
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro Hspec
  have H2 := (syscall_spec_munmap segs ms x8 model _ Hno).mp Hspec
  have H3 := check_munmap_complete_unmodeled (ms_gpr ms 0) (ms_gpr ms 1) model
    (sys_input segs ms x8) (mkEffect (BitVec.ofInt 64 0) [] []) H2
  rw [munmap_check_modeled ms model (mkEffect (BitVec.ofInt 64 0) [] []) Ha] at H3
  repeat' split at H3
  all_goals simp at H3

/- =========================================================================
   mmap: the two families of admissible outcomes
   ========================================================================= -/

theorem ENOMEM_in_mmap_errnos : ENOMEM ∈ mmap_errnos := by
  simp [mmap_errnos]

theorem mmap_errno_range (e : Int) (HIn : e ∈ mmap_errnos) : 1 ≤ e ∧ e ≤ 4095 :=
  errnos_ok_range mmap_errnos e (by decide) HIn

theorem mmap_fail_ok (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (e : Int) (Hno : (x8.toNat : Int) = 222) (Ha : mmap_args_ok ms) (HIn : e ∈ mmap_errnos) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect (errno_ret e) [] []) model []) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  apply (syscall_spec_mmap segs ms x8 model _ Hno).mpr
  apply check_mmap_sound_ok
  unfold check_mmap
  rw [Hoff, Hanon, Hl, Hmb]
  simp only []
  rw [errno_ret_in_intro mmap_errnos e HIn]
  simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, reduceIte, ite_true,
    ite_false]

/-- The [0 ≤ n] hypothesis: call sites discharge it with
    [page_round_up_Z_nonneg]. -/
theorem grant_not_errno (hint : word) (model : Model) (a : word) (n : Int)
    (Hn : 0 ≤ n) (Hg : grant_ok hint model a n = true) :
    errno_ret_in mmap_errnos a = false := by
  obtain ⟨_, _, Hce, _, _⟩ := grant_ok_unpack hint model a n Hg
  apply errno_ret_in_below
  · decide
  · have hroom := alloc_top_room (m_vmmaps model)
    have hs : stack_max_size = 8388608 := rfl
    have h1 : (a.toNat : Int) ≤ alloc_top (m_vmmaps model) := by omega
    unfold two_pow_64 at *
    omega

theorem mmap_succ_ok (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (a : word) (Hno : (x8.toNat : Int) = 222) (Ha : mmap_args_ok ms)
    (Hg : grant_ok (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  obtain ⟨_, _, Hflags, _, _⟩ := Ha
  apply (syscall_spec_mmap segs ms x8 model _ Hno).mpr
  apply check_mmap_sound_ok
  obtain ⟨Hg1, Hg2, Hg3, Hg4, Hg5⟩ := grant_ok_unpack (ms_gpr ms 0) model a _ Hg
  unfold check_mmap
  rw [Hoff, Hanon, Hl, Hmb]
  simp only []
  have hn : 0 ≤ page_round_up_Z ((ms_gpr ms 1).toNat : Int) :=
    page_round_up_Z_nonneg _ (Int.natCast_nonneg _)
  rw [grant_not_errno (ms_gpr ms 0) model a _ hn Hg]
  have hnr : mmap_noreserve_b (BitVec.ofInt 64 34) = false := by decide
  have hcond1 : decide ((a.toNat : Int) % page_size = 0) = true := by
    simp only [decide_eq_true_eq]
    exact Hg1
  have hcond2 : decide (0 < (a.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hg2
  have hcond3 : decide ((a.toNat : Int) + page_round_up_Z ((ms_gpr ms 1).toNat : Int) ≤
      alloc_top (m_vmmaps model)) = true := by
    simp only [decide_eq_true_eq]
    exact Hg3
  have hcond4 : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) a
      (BitVec.ofInt 64 (page_round_up_Z ((ms_gpr ms 1).toNat : Int))) = true := Hg4
  have hcond5 : mmap_noreserve_backed_ok (ms_gpr ms 3) model
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true := by
    unfold mmap_noreserve_backed_ok
    rw [Hflags]
    simp only [hnr, Bool.false_eq_true, ite_false]
    simp only [decide_eq_true_eq]
    exact Hg5
  have hcond6 : listNN_eqb [(a, page_round_up (ms_gpr ms 1))]
      [(a, BitVec.ofInt 64 (page_round_up_Z ((ms_gpr ms 1).toNat : Int)))] = true := by
    simp only [page_round_up, listNN_eqb_eq]
  rw [hcond1, hcond2, hcond3, hcond4, hcond5, hcond6]
  simp only [Bool.true_and, ite_true]
  unfold with_mmap_backing
  rw [Hflags, hnr]
  simp only [Bool.false_eq_true, ite_false]
  unfold mmap_model page_round_up
  rfl

theorem mmap_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : (x8.toNat : Int) = 222) (Ha : mmap_args_ok ms)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)) :
    evs = [] ∧
    ((∃ e, e ∈ mmap_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧ model' = model) ∨
     (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true ∧
        eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))] ∧
        model' = mmap_model a (page_round_up (ms_gpr ms 1)) model)) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  obtain ⟨_, _, Hflags, _, _⟩ := Ha
  have H2 := (syscall_spec_mmap segs ms x8 model _ Hno).mp Hspec
  have H3 := check_mmap_complete_ok (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
    (ms_gpr ms 4) (ms_gpr ms 5) eff model model' evs (sys_input segs ms x8) H2
  unfold check_mmap at H3
  rw [Hoff, Hanon, Hl, Hmb] at H3
  simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, reduceIte, ite_true,
    ite_false] at H3
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws with
  | cons _ _ => simp at H3
  | nil =>
    cases us with
    | cons _ _ => simp at H3
    | nil =>
      cases cs with
      | cons _ _ => simp at H3
      | nil =>
        cases ci with
        | cons _ _ => simp at H3
        | nil =>
          simp only [] at H3
          by_cases Herr : errno_ret_in mmap_errnos r = true
          · rw [ite_eq_left Herr] at H3
            cases zs with
            | cons _ _ => simp at H3
            | nil =>
              obtain ⟨hmm, hev⟩ := check_result.CheckOk.inj H3
              have hrr : ∃ e, e ∈ mmap_errnos ∧ r = errno_ret e :=
                (errno_ret_in_true mmap_errnos r).mp Herr
              obtain ⟨e, hmem, heq⟩ := hrr
              refine ⟨hev.symm, Or.inl ⟨e, hmem, ?_, hmm.symm⟩⟩
              simp only [mkEffect, heq]
          · rw [ite_eq_right Herr] at H3
            split at H3
            · rename_i hcond
              obtain ⟨hmm, hev⟩ := check_result.CheckOk.inj H3
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              obtain ⟨⟨⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩, hg5⟩, hg6⟩ := hcond
              have hdec5 : decide (vm_backing_used model +
                  page_round_up_Z ((ms_gpr ms 1).toNat : Int) ≤ (m_vmmaps model).vm_limit) = true := by
                have h5 := hg5
                unfold mmap_noreserve_backed_ok at h5
                rw [Hflags] at h5
                have hnr : mmap_noreserve_b (BitVec.ofInt 64 34) = false := by decide
                rw [hnr] at h5
                simpa using h5
              have hz : zs = [(r, BitVec.ofInt 64 (page_round_up_Z ((ms_gpr ms 1).toNat : Int)))] :=
                (listNN_eqb_eq _ _).mp hg6
              have hd1 : decide ((r.toNat : Int) % page_size = 0) = true := by
                simp only [decide_eq_true_eq]
                exact hg1
              have hd2 : decide (0 < (r.toNat : Int)) = true := by
                simp only [decide_eq_true_eq]
                exact hg2
              have hd3 : decide ((r.toNat : Int) +
                  page_round_up_Z ((ms_gpr ms 1).toNat : Int) ≤
                  alloc_top (m_vmmaps model)) = true := by
                simp only [decide_eq_true_eq]
                exact hg3
              refine ⟨hev.symm, Or.inr ⟨r, ?_, ?_, ?_⟩⟩
              · unfold grant_ok
                rw [hd1, hd2, hd3, hg4, hdec5]
                rfl
              · simp only [mkEffect, page_round_up, hz]
              · rw [hmm.symm, Hflags]
                have hnr : mmap_noreserve_b (BitVec.ofInt 64 34) = false := by decide
                unfold with_mmap_backing
                rw [hnr]
                simp only [Bool.false_eq_true, ite_false]
                unfold mmap_model page_round_up
                rfl
            · simp at H3

theorem mmap_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (Hno : (x8.toNat : Int) = 222) (Ha : mmap_args_ok ms) :
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro Hspec
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_gates ms Ha
  have H2 := (syscall_spec_mmap segs ms x8 model _ Hno).mp Hspec
  have H3 := check_mmap_complete_unmodeled (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
    (ms_gpr ms 4) (ms_gpr ms 5) model (sys_input segs ms x8) (mkEffect (BitVec.ofInt 64 0) [] []) H2
  unfold check_mmap at H3
  rw [Hoff, Hanon, Hl, Hmb] at H3
  simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, reduceIte, ite_true,
    ite_false] at H3
  repeat' split at H3
  all_goals simp at H3

/- =========================================================================
   Post-syscall state collapses
   ========================================================================= -/

/-- A successful grant's post-state: a0 := a, the granted page range
    reads as zeros, PC advances past the ecall. -/
theorem adv_mmap_grant (regs : BvMap word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (a n : word) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom }
      (mkEffect a [] [(a, n)]))
    = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom := by
  have hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem := by
    funext x
    simp only [apply_unmaps, apply_zeros, zeros_cover, zfill, zmem, List.any_cons,
      List.any_nil, Bool.or_false]
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  simp only [apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc, h10,
    apply_writes, apply_copies, mkEffect, hm, Bool.false_eq_true, reduceIte,
    mkst, regupd, b_npc4]

/- =========================================================================
   The unmapped-range overlay (munmap)
   ========================================================================= -/

/-- After [munmap(a, n)] the covered range is UNMAPPED: every address
    in [a, a+n) reads [none] (a later access faults), everything else
    is untouched.  Coverage is checked in [Int] over unsigned values,
    like [zfill] (recorded mapping ranges never wrap). -/
def unfill (a n : word) (m : word → Option byte) : word → Option byte :=
  fun x =>
    if decide ((a.toNat : Int) ≤ (x.toNat : Int)) &&
       decide ((x.toNat : Int) < (a.toNat : Int) + (n.toNat : Int))
    then none else m x

theorem unfill_out (a n : word) (m : word → Option byte) (x : word)
    (Hx : (x.toNat : Int) < (a.toNat : Int) ∨
          (a.toNat : Int) + (n.toNat : Int) ≤ (x.toNat : Int)) :
    unfill a n m x = m x := by
  unfold unfill
  rcases Hx with Hx | Hx
  · have h1 : decide ((a.toNat : Int) ≤ (x.toNat : Int)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [h1]
    rfl
  · have h2 : decide ((x.toNat : Int) < (a.toNat : Int) + (n.toNat : Int)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [h2, Bool.and_false]
    rfl

theorem rdn_unfill_out (segs : List Segment) (a n : word) (m : word → Option byte)
    (x : word) (k : Nat)
    (Hnw : (x.toNat : Int) + (k : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hd : (x.toNat : Int) + (k : Int) ≤ (a.toNat : Int) ∨
          (a.toNat : Int) + (n.toNat : Int) ≤ (x.toNat : Int)) :
    rdn segs (unfill a n m) x k = rdn segs m x k := by
  apply rdn_ext segs k
  · exact Hnw
  · intro y Hy
    apply unfill_out
    omega

/-- A munmap effect's post-state: a0 := 0, the unmapped range reads as
    unmapped, PC advances past the ecall. -/
theorem adv_munmap (regs : BvMap word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (a n : word) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom }
      (SyscallEffect.mkEffectU (BitVec.ofInt 64 0) [] [] [(a, n)] [] []))
    = mkst (regupd regs 10 (BitVec.ofInt 64 0)) (v_addi pc 4) (unfill a n mem) rom := by
  have hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem := by
    funext x
    simp only [apply_writes, apply_zeros, apply_unmaps, zeros_cover, unfill, List.any_cons,
      List.any_nil, Bool.or_false]
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  simp only [apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc, h10,
    apply_copies, hm, Bool.false_eq_true, reduceIte, mkst, regupd, b_npc4]

/- =========================================================================
   twm: writes/munmap/exit straight line, model threaded
   ========================================================================= -/

/- The put-style retry loop realizing one buffer: a write-pending state
   offering the remainder [rest]; the environment delivers any nonempty
   prefix, the loop reissues on the rest.  The trace contribution of the
   whole node is exactly the FULL buffer (WallSim's [to_wall] shape,
   inlined here because the continuation is the mutual [twm]). -/
mutual
inductive twm (segs : List Segment) : machine_state → Model → List (List byte) → word → Prop where
  | exit (ms : machine_state) (model : Model) (x8 : word)
      (hsvc : ms.ms_svc_pending = some x8) (hx8 : is_exit_no x8) :
      twm segs ms model [] (ms_gpr ms 0 &&& BitVec.ofInt 64 255)
  | write (ms : machine_state) (model : Model) (buf : List byte) (bufs : List (List byte))
      (code : word) (hne : 1 ≤ buf.length)
      (hp : twm_pend segs ms model buf bufs code) :
      twm segs ms model (buf :: bufs) code
  | munmap (ms : machine_state) (model : Model) (x8 : word) (bufs : List (List byte))
      (code : word) (hsvc : ms.ms_svc_pending = some x8) (hno : (x8.toNat : Int) = 215)
      (hargs : munmap_args_ok ms model)
      (hte : twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code) :
      twm segs ms model bufs code
  | step (ms ms' : machine_state) (model : Model) (bufs : List (List byte)) (code : word)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hte : twm segs ms' model bufs code) :
      twm segs ms model bufs code
inductive twm_pend (segs : List Segment) :
    machine_state → Model → List byte → List (List byte) → word → Prop where
  | write (ms : machine_state) (model : Model) (x8 : word) (rest : List byte)
      (bufs : List (List byte)) (code : word)
      (hsvc : ms.ms_svc_pending = some x8) (hno : (x8.toNat : Int) = 64)
      (h0 : ms_gpr ms 0 = BitVec.ofInt 64 1)
      (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest)
      (hne : 1 ≤ rest.length)
      (hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code) :
      twm_pend segs ms model rest bufs code
inductive twm_tail (segs : List Segment) :
    machine_state → Model → List byte → List (List byte) → word → Prop where
  | done (ms : machine_state) (model : Model) (bufs : List (List byte)) (code : word)
      (hte : twm segs ms model bufs code) :
      twm_tail segs ms model [] bufs code
  | more (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hne : 1 ≤ rest.length)
      (hp : twm_pend segs ms model rest bufs code) :
      twm_tail segs ms model rest bufs code
  | step (ms ms' : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (ht : twm_tail segs ms' model rest bufs code) :
      twm_tail segs ms model rest bufs code
end

theorem msteps_twm (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (H : msteps segs ms ms')
    (Hw : twm segs ms' model bufs code) : twm segs ms model bufs code := by
  induction H with
  | mst_refl => exact Hw
  | mst_step ms ms' ms'' hsvc hstep h ih =>
    exact twm.step (ms := ms) (ms' := ms') (model := model) (bufs := bufs) (code := code)
      hsvc hstep (ih Hw)

theorem msteps_twm_tail (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (rest : List byte) (bufs : List (List byte)) (code : word) (H : msteps segs ms ms')
    (Hw : twm_tail segs ms' model rest bufs code) : twm_tail segs ms model rest bufs code := by
  induction H with
  | mst_refl => exact Hw
  | mst_step ms ms' ms'' hsvc hstep h ih =>
    exact twm_tail.step (ms := ms) (ms' := ms') (model := model) (rest := rest)
      (bufs := bufs) (code := code) hsvc hstep (ih Hw)

/- -------------------------------------------------------------------------
   Ergonomic raw-ecall-record constructors
   ------------------------------------------------------------------------- -/

/-- A write at the raw ecall post-state.  The environment may deliver
    any nonempty prefix, so the continuation is the caller's put-loop
    obligation: per delivered length [n], a [twm_tail] of the remainder
    [skipn n buf]. -/
theorem twm_write_ret (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (buf : List byte)
    (bufs : List (List byte)) (code : word)
    (h17 : ((getr regs 17).toNat : Int) = 64)
    (h10 : reg_get regs 10 = BitVec.ofInt 64 1)
    (hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf)
    (hnb : 1 ≤ buf.length)
    (hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
      twm_tail segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom)
        model (buf.drop n) bufs code) :
    twm segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      model (buf :: bufs) code := by
  have e0 : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
  have e1 : BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide
  have e2 : BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) := by decide
  refine twm.write (hne := hnb) (hp := ?_)
  refine twm_pend.write (hsvc := rfl) (hno := h17) (h0 := ?_) (hr := ?_) (hne := hnb)
    (hcont := ?_)
  · simp only [ms_gpr, e0]
    exact h10
  · simp only [ms_gpr, e1, e2]
    exact hr
  · intro n hn1 hn2
    rw [adv_set]
    exact hcont n hn1 hn2

/-- The reissued write at the raw ecall post-state, INSIDE a retry
    loop: the wall-tail counterpart of [twm_write_ret]. -/
theorem twm_tail_write_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (rest : List byte)
    (bufs : List (List byte)) (code : word)
    (h17 : ((getr regs 17).toNat : Int) = 64)
    (h10 : reg_get regs 10 = BitVec.ofInt 64 1)
    (hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some rest)
    (hnb : 1 ≤ rest.length)
    (hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
      twm_tail segs (mkst (regupd regs 10 (len_word (rest.take n))) (v_addi pc 4) mem rom)
        model (rest.drop n) bufs code) :
    twm_tail segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      model rest bufs code := by
  have e0 : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
  have e1 : BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide
  have e2 : BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) := by decide
  refine twm_tail.more (hne := hnb) (hp := ?_)
  refine twm_pend.write (hsvc := rfl) (hno := h17) (h0 := ?_) (hr := ?_) (hne := hnb)
    (hcont := ?_)
  · simp only [ms_gpr, e0]
    exact h10
  · simp only [ms_gpr, e1, e2]
    exact hr
  · intro n hn1 hn2
    rw [adv_set]
    exact hcont n hn1 hn2

/-- A munmap at the raw ecall post-state: a0 := 0, mapping dropped,
    the unmapped range now reads as unmapped.  [a]/[nlen] name the
    addr/len register values so call sites can pre-normalize them. -/
theorem twm_munmap_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (bufs : List (List byte))
    (code a nlen : word)
    (h17 : ((getr regs 17).toNat : Int) = 215)
    (ha : reg_get regs 10 = a) (hn : reg_get regs 11 = nlen)
    (hal : a.toNat % page_size = 0)
    (hlen : nlen ≠ BitVec.ofInt 64 0)
    (hnw : (a.toNat : Int) + page_round_up_Z (nlen.toNat : Int) ≤ TASK_SIZE)
    (hhas : map_has (m_vmmaps model).vm_maps a (page_round_up nlen) = true)
    (hcont : twm segs (mkst (regupd regs 10 (BitVec.ofInt 64 0)) (v_addi pc 4)
      (unfill a (page_round_up nlen) mem) rom) (munmap_model a (page_round_up nlen) model)
      bufs code) :
    twm segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      model bufs code := by
  have e0 : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
  have e1 : BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide
  refine twm.munmap (hsvc := rfl) (hno := h17) (hargs := ?_) (hte := ?_)
  · unfold munmap_args_ok
    simp only [ms_gpr, e0, e1, ha, hn]
    exact ⟨hal, hlen, hnw, hhas⟩
  · simp only [munmap_eff, ms_gpr, e0, e1, ha, hn]
    rw [adv_munmap]
    exact hcont

/-- Bitvector [&&&] with 255 is the identity on a small code. -/
theorem land_255_small (c : word) (hc : (c.toNat : Int) < 256) :
    c &&& BitVec.ofInt 64 255 = c := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (BitVec.ofInt 64 255 : word).toNat = 255 := rfl
  rw [BitVec.toNat_and, h255]
  have hlt : c.toNat < 2 ^ 8 := by omega
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by decide,
    Nat.and_two_pow_sub_one_of_lt_two_pow hlt]

/-- Exit with an arbitrary small code at the raw ecall post-state. -/
theorem twm_exit_coden (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (c : word)
    (h17 : ((getr regs 17).toNat : Int) = 93)
    (h10 : reg_get regs 10 = c) (hc : (c.toNat : Int) < 256) :
    twm segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      model [] c := by
  have e0 : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
  have hg : ms_gpr (⟨regs, fx.fp_regs, pc, some (getr regs 17), none, fx.fp_csr, mem, rom⟩ :
        machine_state) 0 &&& BitVec.ofInt 64 255 = c := by
    simp only [ms_gpr, e0, h10]
    apply land_255_small
    exact hc
  rw [← hg]
  refine twm.exit (segs := segs)
    (ms := ⟨regs, fx.fp_regs, pc, some (getr regs 17), none, fx.fp_csr, mem, rom⟩)
    (model := model) (x8 := getr regs 17) (hx8 := Or.inl h17) (hsvc := ?_)
  rfl

/- -------------------------------------------------------------------------
   One-step inversion for a munmap config.
   ------------------------------------------------------------------------- -/

theorem sstep_munmap_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 215)
    (Hargs : munmap_args_ok ms model)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    evs = [] ∧
    st = .SNext ⟨advance_past_svc (apply_effect ms (munmap_eff ms)),
      munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model⟩ := by
  cases Hss with
  | instr _ _ _ _ hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault _ _ hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled _ _ hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall _ _ x80 eff model1 model2 _ hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨heff, hmodel, hevs⟩ := munmap_ok_inv segs ms x8 model eff model1 evs Hno Hargs hspec
    subst heff
    subst hmodel
    subst hevs
    rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy)] at hmat
    obtain rfl := Option.some.inj hmat
    exact ⟨rfl, rfl⟩
  | syscall_materialization_fault _ _ x80 eff model1 evs0 hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨heff, hmodel, hevs⟩ := munmap_ok_inv segs ms x8 model eff model1 evs0 Hno Hargs hspec
    subst heff
    subst hmodel
    subst hevs
    rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy)] at hmat
    exact absurd hmat (by simp)
  | exit _ _ x80 eff model1 evs0 code hh hsvc hspec hh' hk =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨heff, hmodel, hevs⟩ := munmap_ok_inv segs ms x8 model eff model1 evs0 Hno Hargs hspec
    subst heff
    subst hmodel
    subst hevs
    rw [munmap_model_halted, Hh] at hh'
    exact absurd hh' (by simp)
  | killed _ _ x80 eff model1 evs0 sig hh hsvc hspec hk =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨heff, hmodel, hevs⟩ := munmap_ok_inv segs ms x8 model eff model1 evs0 Hno Hargs hspec
    subst heff
    subst hmodel
    subst hevs
    have hhn : m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = none := by
      rw [munmap_model_halted]
      exact Hh
    rw [m_killed_of_m_halted_none _ hhn] at hk
    exact absurd hk (by simp)
  | syscall_unmodeled _ _ x80 hh hsvc hspec =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    exact absurd hspec (munmap_no_unmodeled segs ms x8 model Hno Hargs)

/- -------------------------------------------------------------------------
   Trace characterization of [twm].
   ------------------------------------------------------------------------- -/

/- The omni reading of [twm]: one mutual induction gives the exact trace,
   termination and error-freedom for every chunking of every wall node. -/

def twm_post (bufs : List (List byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = wevents bufs ++ [event.ExitEv code fs] ∧ exits_with code tr o

def twm_rest_post (rest : List byte) (bufs : List (List byte)) (code : word)
    (fs : Fs.Fs) : post :=
  fun tr o =>
    tr = rest.map (event.WriteEv (BitVec.ofInt 64 1)) ++ wevents bufs ++ [event.ExitEv code fs] ∧
    exits_with code tr o

/- =========================================================================
   tmw: deterministic prefix, then the branching mmap
   ========================================================================= -/

inductive tmw (segs : List Segment) :
    machine_state → Model → List (List byte) → word → List (List byte) → word → Prop where
  | mmap (ms : machine_state) (model : Model) (x8 : word)
      (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
      (hsvc : ms.ms_svc_pending = some x8) (hno : (x8.toNat : Int) = 222)
      (hargs : mmap_args_ok ms)
      (hfail : ∀ e, e ∈ mmap_errnos →
        twm segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf)
      (hsucc : ∀ a, grant_ok (ms_gpr ms 0) model a
          (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
        twm segs
          (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs)
      (hex : ∃ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
      tmw segs ms model bf cf bs cs
  | step (ms ms' : machine_state) (model : Model) (bf : List (List byte)) (cf : word)
      (bs : List (List byte)) (cs : word)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hte : tmw segs ms' model bf cf bs cs) :
      tmw segs ms model bf cf bs cs

theorem msteps_tmw (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (H : msteps segs ms ms') (Hw : tmw segs ms' model bf cf bs cs) :
    tmw segs ms model bf cf bs cs := by
  induction H with
  | mst_refl => exact Hw
  | mst_step ms ms' ms'' hsvc hstep h ih =>
    exact tmw.step (ms := ms) (ms' := ms') (model := model) (bf := bf) (cf := cf) (bs := bs)
      (cs := cs) hsvc hstep (ih Hw)

/-- Raw-ecall-record constructor for the mmap node: the register file
    and memory are exposed, and the two continuations are collapsed to
    [mkst] form ([adv_set] / [adv_mmap_grant]). -/
theorem tmw_mmap_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (bf : List (List byte)) (cf : word)
    (bs : List (List byte)) (cs : word)
    (h17 : ((getr regs 17).toNat : Int) = 222)
    (h11 : reg_get regs 11 ≠ BitVec.ofInt 64 0)
    (h12 : reg_get regs 12 = BitVec.ofInt 64 3)
    (h13 : reg_get regs 13 = BitVec.ofInt 64 34)
    (h14 : reg_get regs 14 = BitVec.ofInt 64 (-1))
    (h15 : reg_get regs 15 = BitVec.ofInt 64 0)
    (hfail : ∀ e, e ∈ mmap_errnos →
      twm segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf)
    (hsucc : ∀ a, grant_ok (reg_get regs 10) model a
        (page_round_up_Z ((reg_get regs 11).toNat : Int)) = true →
      twm segs (mkst (regupd regs 10 a) (v_addi pc 4)
        (zfill a (page_round_up (reg_get regs 11)) mem) rom)
        (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs)
    (hex : ∃ a, grant_ok (reg_get regs 10) model a
      (page_round_up_Z ((reg_get regs 11).toNat : Int)) = true) :
    tmw segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      model bf cf bs cs := by
  have e0 : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) := by decide
  have e1 : BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) := by decide
  have e2 : BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) := by decide
  have e3 : BitVec.ofInt 5 (10 + ((3 : Nat) : Int)) = (13 : reg) := by decide
  have e4 : BitVec.ofInt 5 (10 + ((4 : Nat) : Int)) = (14 : reg) := by decide
  have e5 : BitVec.ofInt 5 (10 + ((5 : Nat) : Int)) = (15 : reg) := by decide
  refine tmw.mmap (hsvc := rfl) (hno := h17) (hargs := ?_) (hfail := ?_) (hsucc := ?_)
    (hex := ?_)
  · unfold mmap_args_ok
    simp only [ms_gpr, e1, e2, e3, e4, e5]
    exact ⟨h11, h12, h13, h14, h15⟩
  · intro e he
    rw [adv_set]
    exact hfail e he
  · intro a hg
    simp only [ms_gpr, e1]
    rw [adv_mmap_grant]
    exact hsucc a hg
  · simp only [ms_gpr, e0, e1]
    exact hex

/- -------------------------------------------------------------------------
   One-step inversion for the mmap config.
   ------------------------------------------------------------------------- -/

theorem sstep_mmap_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    evs = [] ∧
    ((∃ e, e ∈ mmap_errnos ∧
        st = .SNext ⟨advance_past_svc (set_gpr0 ms (errno_ret e)), model⟩) ∨
     (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true ∧
        st = .SNext ⟨advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])),
          mmap_model a (page_round_up (ms_gpr ms 1)) model⟩)) := by
  cases Hss with
  | instr _ _ _ _ hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault _ _ hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled _ _ hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall _ _ x80 eff model1 model2 _ hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨hevs, hcase⟩ := mmap_ok_inv segs ms x8 model eff model1 evs Hno Hargs hspec
    subst hevs
    rcases hcase with ⟨e, hmem, heff, hmodel⟩ | ⟨a, hg, heff, hmodel⟩
    · subst heff
      subst hmodel
      rw [materialize_model_accesses_no_lazy _ _ Hlazy] at hmat
      obtain rfl := Option.some.inj hmat
      exact ⟨rfl, Or.inl ⟨e, hmem, rfl⟩⟩
    · subst heff
      subst hmodel
      rw [materialize_model_accesses_no_lazy _ _
        (by rw [mmap_model_lazy]; exact Hlazy)] at hmat
      obtain rfl := Option.some.inj hmat
      exact ⟨rfl, Or.inr ⟨a, hg, rfl⟩⟩
  | syscall_materialization_fault _ _ x80 eff model1 evs0 hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨hevs, hcase⟩ := mmap_ok_inv segs ms x8 model eff model1 evs0 Hno Hargs hspec
    subst hevs
    rcases hcase with ⟨e, hmem, heff, hmodel⟩ | ⟨a, hg, heff, hmodel⟩
    · subst heff
      subst hmodel
      rw [materialize_model_accesses_no_lazy _ _ Hlazy] at hmat
      exact absurd hmat (by simp)
    · subst heff
      subst hmodel
      rw [materialize_model_accesses_no_lazy _ _
        (by rw [mmap_model_lazy]; exact Hlazy)] at hmat
      exact absurd hmat (by simp)
  | exit _ _ x80 eff model1 evs0 code hh hsvc hspec hh' hk =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨hevs, hcase⟩ := mmap_ok_inv segs ms x8 model eff model1 evs0 Hno Hargs hspec
    rcases hcase with ⟨e, hmem, heff, hmodel⟩ | ⟨a, hg, heff, hmodel⟩
    · subst heff
      subst hmodel
      rw [Hh] at hh'
      exact absurd hh' (by simp)
    · subst heff
      subst hmodel
      rw [mmap_model_halted, Hh] at hh'
      exact absurd hh' (by simp)
  | killed _ _ x80 eff model1 evs0 sig hh hsvc hspec hk =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨hevs, hcase⟩ := mmap_ok_inv segs ms x8 model eff model1 evs0 Hno Hargs hspec
    rcases hcase with ⟨e, hmem, heff, hmodel⟩ | ⟨a, hg, heff, hmodel⟩
    · subst heff
      subst hmodel
      rw [m_killed_of_m_halted_none _ Hh] at hk
      exact absurd hk (by simp)
    · subst heff
      subst hmodel
      have hhn : m_halted (mmap_model a (page_round_up (ms_gpr ms 1)) model) = none := by
        rw [mmap_model_halted]
        exact Hh
      rw [m_killed_of_m_halted_none _ hhn] at hk
      exact absurd hk (by simp)
  | syscall_unmodeled _ _ x80 hh hsvc hspec =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    exact absurd hspec (mmap_no_unmodeled segs ms x8 model Hno Hargs)

/- -------------------------------------------------------------------------
   Trace characterization of [tmw].
   ------------------------------------------------------------------------- -/

/-- The omni reading of [tmw]: every execution takes one of the two
    branches at the mmap node and then runs its [twm] straight line. -/
def tmw_post (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (fs : Fs.Fs) : post :=
  fun tr o =>
    (tr = wevents bf ++ [event.ExitEv cf fs] ∧ exits_with cf tr o) ∨
    (tr = wevents bs ++ [event.ExitEv cs fs] ∧ exits_with cs tr o)

/-- The two candidate traces. -/
def two_traces (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (fs : Fs.Fs) (tr : List event) : Prop :=
  is_prefix tr (wevents bf ++ [event.ExitEv cf fs]) ∨
  is_prefix tr (wevents bs ++ [event.ExitEv cs fs])

theorem two_traces_prefix_closed (bf : List (List byte)) (cf : word) (bs : List (List byte))
    (cs : word) (fs : Fs.Fs) (tr tr' : List event)
    (H : two_traces bf cf bs cs fs tr) (Hp : is_prefix tr' tr) :
    two_traces bf cf bs cs fs tr' := by
  rcases H with H | H
  · exact Or.inl (is_prefix_trans Hp H)
  · exact Or.inr (is_prefix_trans Hp H)

/-! -/

example : page_round_up (BitVec.ofInt 64 4096) = BitVec.ofInt 64 4096 := by decide

example : page_round_up (BitVec.ofInt 64 4097) = BitVec.ofInt 64 8192 := by decide

example : ((BitVec.ofInt 64 0) &&& BitVec.ofInt 64 255) = (BitVec.ofInt 64 0) := by decide

example : zfill (BitVec.ofInt 64 8) (BitVec.ofInt 64 2) (fun _ => some 7) (BitVec.ofInt 64 9)
    = some (BitVec.ofInt 8 0) := by decide

example : unfill (BitVec.ofInt 64 8) (BitVec.ofInt 64 2) (fun _ => some 7) (BitVec.ofInt 64 9)
    = none := by decide

example : unfill (BitVec.ofInt 64 8) (BitVec.ofInt 64 2) (fun _ => some 7) (BitVec.ofInt 64 10)
    = some 7 := by decide

example : wevents [[2, 3], [4]]
    = [event.WriteEv (BitVec.ofInt 64 1) 2, event.WriteEv (BitVec.ofInt 64 1) 3,
       event.WriteEv (BitVec.ofInt 64 1) 4] := by decide


/- =========================================================================
   The omni reading of [twm]
   ========================================================================= -/

theorem twm_exec_mut (segs : List Segment) :
    (∀ (ms : machine_state) (model : Model) (bufs : List (List byte)) (code : word),
      twm segs ms model bufs code → bufs_modeled bufs → m_halted model = none →
      m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model))) ∧
    (∀ (ms : machine_state) (model : Model) (rest : List byte) (bufs : List (List byte))
      (code : word),
      twm_pend segs ms model rest bufs code → buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model))) ∧
    (∀ (ms : machine_state) (model : Model) (rest : List byte) (bufs : List (List byte))
      (code : word),
      twm_tail segs ms model rest bufs code → buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model))) := by
  have c_exit : ∀ (ms : machine_state) (model : Model) (x8 : word)
      (hsvc : ms.ms_svc_pending = some x8) (hx8 : is_exit_no x8),
      bufs_modeled [] → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩
        (twm_post [] (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)) := by
    intro ms model x8 hsvc hx8 hbm hh hlazy hfd
    refine exec_step_only segs ⟨ms, model⟩
      (twm_post [] (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model))
      [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
      ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ ?_ ?_ ?_
    · exact sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms 0 &&& BitVec.ofInt 64 255) hh hsvc
        (exit_dispatch_ok (sys_input segs ms x8) model (by
          rw [in_sysno_sys_input]; exact hx8))
        (by simp [m_halted_with_halted]) (by simp [m_killed_with_halted])
    · intro evs st hss
      exact sstep_exit_inv segs ms model x8 evs st hh hsvc hx8 hss
    · refine exec_halted segs
        ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ _ ?_ ?_
      · simp [m_halted_with_halted]
      · refine ⟨?_, ?_, ?_⟩
        · simp [twm_post, wevents]
        · simp [m_halted_with_halted]
        · simp [m_killed_with_halted]
  have c_write : ∀ (ms : machine_state) (model : Model) (buf : List byte)
      (bufs : List (List byte)) (code : word) (hne : 1 ≤ buf.length)
      (hp : twm_pend segs ms model buf bufs code),
      (buf_modeled buf → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
        fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post buf bufs code (m_fs model))) →
      bufs_modeled (buf :: bufs) → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_post (buf :: bufs) code (m_fs model)) := by
    intro ms model buf bufs code hne hp ih hbm hh hlazy hfd
    have hb : buf_modeled buf := hbm buf (by simp)
    have hbs : bufs_modeled bufs := fun b hb' => hbm b (by simp [hb'])
    refine exec_conseq segs ⟨ms, model⟩ _ _ (ih hb hbs hh hlazy hfd) ?_
    intro tr o h
    obtain ⟨htr, hx⟩ := h
    refine ⟨?_, hx⟩
    simp only [twm_rest_post, twm_post, wevents] at htr ⊢
    rw [htr]
  have c_munmap : ∀ (ms : machine_state) (model : Model) (x8 : word)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 215) (hargs : munmap_args_ok ms model)
      (hte : twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code),
      (bufs_modeled bufs →
        m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = none →
        m_vm_lazy (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = [] →
        fd1chan (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) →
        OmniRun.exec segs
          ⟨advance_past_svc (apply_effect ms (munmap_eff ms)),
            munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model⟩
          (twm_post bufs code
            (m_fs (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)))) →
      bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)) := by
    intro ms model x8 bufs code hsvc hno hargs hte ih hbm hh hlazy hfd
    have hh' : m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = none := by
      rw [munmap_model_halted]
      exact hh
    have hfd' : fd1chan (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) :=
      munmap_model_fd1chan _ _ _ hfd
    refine exec_step_only segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)) []
      ⟨advance_past_svc (apply_effect ms (munmap_eff ms)),
        munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model⟩ ?_ ?_ ?_
    · exact sstep.syscall ms model x8 (munmap_eff ms)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [] hh hsvc
        (munmap_ok segs ms x8 model hno hargs) hh'
        (by rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ hlazy)])
    · intro evs st hss
      exact sstep_munmap_inv segs ms model x8 evs st hh hlazy hsvc hno hargs hss
    · refine exec_conseq segs _ _ _
        (ih hbm hh' (munmap_model_no_lazy _ _ _ hlazy) hfd') ?_
      intro tr o h
      simpa only [munmap_model_fs, List.nil_append] using h
  have c_step : ∀ (ms ms' : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hte : twm segs ms' model bufs code),
      (bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms', model⟩ (twm_post bufs code (m_fs model))) →
      bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)) := by
    intro ms ms' model bufs code hsvc hstep hte ih hbm hh hlazy hfd
    refine exec_step_only segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)) []
      ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss
    · simpa using ih hbm hh hlazy hfd
  have c_pend : ∀ (ms : machine_state) (model : Model) (x8 : word) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 64) (h0 : ms_gpr ms 0 = BitVec.ofInt 64 1)
      (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest)
      (hne : 1 ≤ rest.length)
      (hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code),
      (∀ (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length),
        buf_modeled (rest.drop n) → bufs_modeled bufs → m_halted model = none →
        m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs
          ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take n))), model⟩
          (twm_rest_post (rest.drop n) bufs code (m_fs model))) →
      buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) := by
    intro ms model x8 rest bufs code hsvc hno h0 hr hne hcont ih hbr hbm hh hlazy hfd
    refine exec.step ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) hh
      ⟨List.map (event.WriteEv (BitVec.ofInt 64 1)) (rest.take rest.length),
        .SNext ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take rest.length))), model⟩, ?_⟩
      ?_ ?_
    · refine sstep.syscall ms model x8 (with_copyins [(ms_gpr ms 1, rest.length)]
          (mkEffect (len_word (rest.take rest.length)) [] [])) model model _ hh hsvc ?_ hh ?_
      · exact write1_ok_n segs ms x8 model rest rest.length hfd hno h0 hr hbr hne
          (Nat.le_refl _)
      · rw [materialize_model_accesses_no_lazy model _ hlazy]
    · intro evs hss
      obtain ⟨n, -, -, -, hst⟩ :=
        sstep_write_inv segs ms model x8 rest evs .SError hh hlazy hfd hsvc hno h0 hr hbr hne hss
      exact absurd hst (by simp)
    · intro evs c' hss
      obtain ⟨n, hn1, hn2, hevs, hc'⟩ :=
        sstep_write_next_inv segs ms model x8 rest evs c' hh hlazy hfd hsvc hno h0 hr hne hss
      rw [hevs, hc']
      refine exec_conseq segs _ _ _
        (ih n hn1 hn2 (buf_modeled_skipn n rest hbr) hbm hh hlazy hfd) ?_
      intro tr o h
      obtain ⟨htr, hx⟩ := h
      refine ⟨?_, hx⟩
      have hmap : List.map (event.WriteEv (BitVec.ofInt 64 1)) rest
          = List.map (event.WriteEv (BitVec.ofInt 64 1)) (rest.take n) ++
            List.map (event.WriteEv (BitVec.ofInt 64 1)) (rest.drop n) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hmap, htr]
      simp only [List.append_assoc]
  have c_done : ∀ (ms : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (hte : twm segs ms model bufs code),
      (bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model))) →
      buf_modeled [] → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post [] bufs code (m_fs model)) := by
    intro ms model bufs code hte ih hbn hbm hh hlazy hfd
    exact ih hbm hh hlazy hfd
  have c_more : ∀ (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hne : 1 ≤ rest.length)
      (hp : twm_pend segs ms model rest bufs code),
      (buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
        fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model))) →
      buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) := by
    intro ms model rest bufs code hne hp ih hbr hbm hh hlazy hfd
    exact ih hbr hbm hh hlazy hfd
  have c_tstep : ∀ (ms ms' : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (ht : twm_tail segs ms' model rest bufs code),
      (buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
        fd1chan model →
        OmniRun.exec segs ⟨ms', model⟩ (twm_rest_post rest bufs code (m_fs model))) →
      buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) := by
    intro ms ms' model rest bufs code hsvc hstep ht ih hbr hbm hh hlazy hfd
    refine exec_step_only segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) []
      ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss
    · simpa using ih hbr hbm hh hlazy hfd
  have rec1 : ∀ (ms : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (d : twm segs ms model bufs code),
      bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)) := by
    intro ms model bufs code d
    exact twm.rec
      (motive_1 := fun ms model bufs code _ => bufs_modeled bufs → m_halted model = none →
        m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)))
      (motive_2 := fun ms model rest bufs code _ => buf_modeled rest → bufs_modeled bufs →
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)))
      (motive_3 := fun ms model rest bufs code _ => buf_modeled rest → bufs_modeled bufs →
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)))
      c_exit c_write c_munmap c_step c_pend c_done c_more c_tstep d
  have rec2 : ∀ (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (d : twm_pend segs ms model rest bufs code),
      buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) := by
    intro ms model rest bufs code d
    exact twm_pend.rec
      (motive_1 := fun ms model bufs code _ => bufs_modeled bufs → m_halted model = none →
        m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)))
      (motive_2 := fun ms model rest bufs code _ => buf_modeled rest → bufs_modeled bufs →
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)))
      (motive_3 := fun ms model rest bufs code _ => buf_modeled rest → bufs_modeled bufs →
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)))
      c_exit c_write c_munmap c_step c_pend c_done c_more c_tstep d
  have rec3 : ∀ (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (d : twm_tail segs ms model rest bufs code),
      buf_modeled rest → bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] →
      fd1chan model →
      OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)) := by
    intro ms model rest bufs code d
    exact twm_tail.rec
      (motive_1 := fun ms model bufs code _ => bufs_modeled bufs → m_halted model = none →
        m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)))
      (motive_2 := fun ms model rest bufs code _ => buf_modeled rest → bufs_modeled bufs →
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)))
      (motive_3 := fun ms model rest bufs code _ => buf_modeled rest → bufs_modeled bufs →
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        OmniRun.exec segs ⟨ms, model⟩ (twm_rest_post rest bufs code (m_fs model)))
      c_exit c_write c_munmap c_step c_pend c_done c_more c_tstep d
  exact ⟨rec1, rec2, rec3⟩

theorem twm_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code) :
    bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    OmniRun.exec segs ⟨ms, model⟩ (twm_post bufs code (m_fs model)) :=
  (twm_exec_mut segs).1 ms model bufs code Hte

theorem twm_star_admits (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    ∃ c, star segs ⟨ms, model⟩ (wevents bufs ++ [event.ExitEv code (m_fs model)]) c := by
  obtain ⟨tr, o, Hm, HQ⟩ :=
    exec_realizes segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
  obtain ⟨Heq, Hx⟩ := HQ
  cases o with
  | OHalt c' =>
    obtain ⟨Hstar, -⟩ := mexec_halt_star segs ⟨ms, model⟩ tr (.OHalt c') Hm c' rfl
    exact ⟨c', by rw [← Heq]; exact Hstar⟩
  | OError c' => exact Hx.elim

theorem twm_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (tr : List event) (c : config)
    (Hstar : star segs ⟨ms, model⟩ tr c) :
    is_prefix tr (wevents bufs ++ [event.ExitEv code (m_fs model)]) := by
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _
      (exec_star segs _ _ tr c (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar)
  obtain ⟨Heq, -⟩ := HQ
  rw [← Heq]
  exact is_prefix_app tr tr'

theorem twm_exec_not_errors (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    ¬ OmniRun.exec segs ⟨ms, model⟩ OmniRun.errors := by
  intro Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes segs _ _ Hex
  obtain ⟨-, Hx⟩ := exec_sound segs _ _
    (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd) tr o Hm
  exact (exits_with_never_errors code tr o Hx) Herr

theorem twm_exec_code_unique (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) (Hte : twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (code' : word)
    (Hex : OmniRun.exec segs ⟨ms, model⟩ (exits_with code')) : code' = code := by
  obtain ⟨tr, o, Hm, -⟩ :=
    exec_realizes segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
  cases o with
  | OHalt c' =>
    have h1 := exec_sound segs _ _ Hex tr (.OHalt c') Hm
    have h2 := exec_sound segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
      tr (.OHalt c') Hm
    simp only [exits_with] at h1
    simp only [twm_post, exits_with] at h2
    have h2' : m_halted c'.cfg_model = some code := h2.2.1
    rw [h2'] at h1
    exact (Option.some.inj h1.1).symm
  | OError c' =>
    have h2 := exec_sound segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
      tr (.OError c') Hm
    simp only [twm_post, exits_with] at h2
    exact h2.2.elim

/- =========================================================================
   The omni reading of [tmw]
   ========================================================================= -/

theorem tmw_exec (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    OmniRun.exec segs ⟨ms, model⟩ (tmw_post bf cf bs cs (m_fs model)) := by
  induction Hte with
  | mmap ms model x8 bf cf bs cs hsvc hno hargs hfail hsucc hex =>
    refine exec.step ⟨ms, model⟩ (tmw_post bf cf bs cs (m_fs model)) Hh
      ⟨[], .SNext ⟨advance_past_svc (set_gpr0 ms (errno_ret ENOMEM)), model⟩, ?_⟩ ?_ ?_
    · exact sstep.syscall ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model []
        Hh hsvc (mmap_fail_ok segs ms x8 model ENOMEM hno hargs ENOMEM_in_mmap_errnos) Hh
        (by rw [materialize_model_accesses_no_lazy model _ Hlazy])
    · intro evs hss
      obtain ⟨hevs, hcase⟩ :=
        sstep_mmap_inv segs ms model x8 evs .SError Hh Hlazy hsvc hno hargs hss
      rcases hcase with ⟨e, -, hst⟩ | ⟨a, -, hst⟩ <;> exact absurd hst (by simp)
    · intro evs c' hss
      obtain ⟨hevs, hcase⟩ :=
        sstep_mmap_inv segs ms model x8 evs (.SNext c') Hh Hlazy hsvc hno hargs hss
      subst hevs
      rcases hcase with ⟨e, he, hst⟩ | ⟨a, hg, hst⟩
      · cases hst
        refine exec_conseq segs _ _ _
          (twm_exec segs _ _ _ _ (hfail e he) Hbf Hh Hlazy Hfd) ?_
        intro tr o h
        exact Or.inl h
      · cases hst
        have hh' : m_halted (mmap_model a (page_round_up (ms_gpr ms 1)) model) = none := by
          rw [mmap_model_halted]
          exact Hh
        have hfd' : fd1chan (mmap_model a (page_round_up (ms_gpr ms 1)) model) :=
          mmap_model_fd1chan _ _ _ Hfd
        refine exec_conseq segs _ _ _
          (twm_exec segs _ _ _ _ (hsucc a hg) Hbs hh'
            (by rw [mmap_model_lazy]; exact Hlazy) hfd') ?_
        intro tr o h
        refine Or.inr ⟨?_, h.2⟩
        rw [h.1, mmap_model_fs]
        simp
  | step ms ms' model bf cf bs cs hsvc hstep hte ih =>
    refine exec_step_only segs ⟨ms, model⟩ (tmw_post bf cf bs cs (m_fs model)) []
      ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hss
    · simpa using ih Hbf Hbs Hh Hlazy Hfd

theorem tmw_star_admits_fail (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    ∃ c, star segs ⟨ms, model⟩ (wevents bf ++ [event.ExitEv cf (m_fs model)]) c := by
  induction Hte with
  | mmap ms model x8 bf cf bs cs hsvc hno hargs hfail hsucc hex =>
    obtain ⟨c, Hstar⟩ :=
      twm_star_admits segs _ _ _ _ (hfail ENOMEM ENOMEM_in_mmap_errnos) Hbf Hh Hlazy Hfd
    exact ⟨c, star.step ⟨ms, model⟩ [] _ _ c
      (sstep.syscall ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model [] Hh hsvc
        (mmap_fail_ok segs ms x8 model ENOMEM hno hargs ENOMEM_in_mmap_errnos) Hh
        (by rw [materialize_model_accesses_no_lazy model _ Hlazy]))
      Hstar⟩
  | step ms ms' model bf cf bs cs hsvc hstep hte ih =>
    obtain ⟨c, Hstar⟩ := ih Hbf Hh Hlazy Hfd
    exact ⟨c, star.step ⟨ms, model⟩ [] ⟨ms', model⟩ _ c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])) Hstar⟩

theorem tmw_star_admits_succ (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    ∃ c, star segs ⟨ms, model⟩ (wevents bs ++ [event.ExitEv cs (m_fs model)]) c := by
  induction Hte with
  | mmap ms model x8 bf cf bs cs hsvc hno hargs hfail hsucc hex =>
    obtain ⟨a, hg⟩ := hex
    have hh' : m_halted (mmap_model a (page_round_up (ms_gpr ms 1)) model) = none := by
      rw [mmap_model_halted]
      exact Hh
    have hfd' : fd1chan (mmap_model a (page_round_up (ms_gpr ms 1)) model) :=
      mmap_model_fd1chan _ _ _ Hfd
    obtain ⟨c, Hstar⟩ :=
      twm_star_admits segs _ _ _ _ (hsucc a hg) Hbs hh'
        (by rw [mmap_model_lazy]; exact Hlazy) hfd'
    rw [mmap_model_fs] at Hstar
    exact ⟨c, star.step ⟨ms, model⟩ [] _ _ c
      (sstep.syscall ms model x8 (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) [] Hh hsvc
        (mmap_succ_ok segs ms x8 model a hno hargs hg) hh'
        (by rw [materialize_model_accesses_no_lazy _ _
          (by rw [mmap_model_lazy]; exact Hlazy)]))
      Hstar⟩
  | step ms ms' model bf cf bs cs hsvc hstep hte ih =>
    obtain ⟨c, Hstar⟩ := ih Hbs Hh Hlazy Hfd
    exact ⟨c, star.step ⟨ms, model⟩ [] ⟨ms', model⟩ _ c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])) Hstar⟩

theorem tmw_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (tr : List event) (c : config) (Hstar : star segs ⟨ms, model⟩ tr c) :
    two_traces bf cf bs cs (m_fs model) tr := by
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _
      (exec_star segs _ _ tr c
        (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar)
  rcases HQ with ⟨Heq, -⟩ | ⟨Heq, -⟩
  · exact Or.inl (by rw [← Heq]; exact is_prefix_app tr tr')
  · exact Or.inr (by rw [← Heq]; exact is_prefix_app tr tr')

/- -------------------------------------------------------------------------
   No-error characterization
   ------------------------------------------------------------------------- -/

/-- No-error: a corollary of [tmw_exec]. -/
theorem tmw_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    ¬ reaches_error segs ⟨ms, model⟩ := by
  refine exec_no_error segs _ ?_
  refine exec_conseq segs _ (tmw_post bf cf bs cs (m_fs model)) never_errors
    (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) ?_
  intro tr o h
  rcases h with ⟨-, hx⟩ | ⟨-, hx⟩
  · exact exits_with_never_errors cf tr o hx
  · exact exits_with_never_errors cs tr o hx

/-- Bites: the judgments name the outcome, so the other readings of the
    same runs are refuted — neither shape errors, [twm] exits with no
    other code, and neither branch of [tmw] alone is the whole run
    (whenever the two traces are not prefixes of one another). -/
theorem tmw_exec_not_errors (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model) :
    ¬ OmniRun.exec segs ⟨ms, model⟩ OmniRun.errors := by
  intro Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes segs _ _ Hex
  have HQ := exec_sound segs _ _
    (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) tr o Hm
  rcases HQ with ⟨-, hx⟩ | ⟨-, hx⟩
  · exact (exits_with_never_errors cf tr o hx) Herr
  · exact (exits_with_never_errors cs tr o hx) Herr

theorem tmw_exec_not_fail_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbs : bufs_modeled bs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hnp : ¬ is_prefix (wevents bs ++ [event.ExitEv cs (m_fs model)])
      (wevents bf ++ [event.ExitEv cf (m_fs model)])) :
    ¬ OmniRun.exec segs ⟨ms, model⟩ (twm_post bf cf (m_fs model)) := by
  intro Hex
  obtain ⟨c, Hstar⟩ := tmw_star_admits_succ segs ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ c Hex Hstar)
  obtain ⟨Heq, -⟩ := HQ
  exact Hnp (by rw [← Heq]; exact is_prefix_app _ _)

theorem tmw_exec_not_succ_only (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs ms model bf cf bs cs) (Hbf : bufs_modeled bf)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hfd : fd1chan model)
    (Hnp : ¬ is_prefix (wevents bf ++ [event.ExitEv cf (m_fs model)])
      (wevents bs ++ [event.ExitEv cs (m_fs model)])) :
    ¬ OmniRun.exec segs ⟨ms, model⟩ (twm_post bs cs (m_fs model)) := by
  intro Hex
  obtain ⟨c, Hstar⟩ := tmw_star_admits_fail segs ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ c Hex Hstar)
  obtain ⟨Heq, -⟩ := HQ
  exact Hnp (by rw [← Heq]; exact is_prefix_app _ _)

/- =========================================================================
   Run-level packaging and the equivalence glue
   ========================================================================= -/

theorem mmap_obs_iff_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (bf : List (List byte)) (cf : word)
    (bs : List (List byte)) (cs : word)
    (Hte : tmw segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) (tr : List event) :
    obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      two_traces bf cf bs cs (in_fs inp) tr := by
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none := rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] := rfl
  have Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp) :=
    init_model_fd1chan _ _ _ _ _ _
  have Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp := rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    have H2 := tmw_star_only segs _ _ bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr' c Hstar
    rw [Hfs] at H2
    exact two_traces_prefix_closed bf cf bs cs (in_fs inp) tr' tr H2 Hp
  · rintro (Hp | Hp)
    · obtain ⟨c, Hstar⟩ := tmw_star_admits_fail segs _ _ bf cf bs cs Hte Hbf Hh Hlazy Hfd
      rw [Hfs] at Hstar
      exact ⟨_, c, Hstar, Hp⟩
    · obtain ⟨c, Hstar⟩ := tmw_star_admits_succ segs _ _ bf cf bs cs Hte Hbs Hh Hlazy Hfd
      rw [Hfs] at Hstar
      exact ⟨_, c, Hstar, Hp⟩

theorem mmap_no_error_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) :=
  tmw_no_error segs _ (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs
    rfl rfl (init_model_fd1chan _ _ _ _ _ _) Hte Hbf Hbs

/-- The run-level omni judgment of a fail-or-succeed mmap run, at the two
    role budgets. -/
theorem mmap_omni_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hte : tmw segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (tmw_post bf cf bs cs (in_fs inp)) := by
  show OmniRun.exec segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (tmw_post bf cf bs cs (in_fs inp))
  exact tmw_exec segs _ _ bf cf bs cs Hte Hbf Hbs rfl rfl (init_model_fd1chan _ _ _ _ _ _)

theorem mmap_omni_strong_equiv_te
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word)
    (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hsource : tmw source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      bf cf bs cs)
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  constructor
  · refine coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
          bf cf bs cs Hsource Hbf Hbs)) ?_
    intro tr o h
    rcases h with ⟨-, hx⟩ | ⟨-, hx⟩
    · exact never_errors_covered source_segs tr o (exits_with_never_errors cf tr o hx)
    · exact never_errors_covered source_segs tr o (exits_with_never_errors cs tr o hx)
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
        bf cf bs cs Hsource Hbf Hbs tr).trans
        (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
          bf cf bs cs Htarget Hbf Hbs tr).symm
    · refine (bh_errors_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bf cf bs cs Htarget Hbf Hbs

/-- The [Equivalence]-level equivalence for two one-mmap binaries whose
    failure tails and success tails agree. -/
theorem mmap_strong_equiv_te
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word)
    (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo) (asp abrk amb : word)
    (arnd : EntryDraw) (alim : Int)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hsource : tmw source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) bf cf bs cs)
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp) ∧
    equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (mmap_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
        Hsource Hbf Hbs)
  · right
    constructor
    · intro tr
      exact (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
        Hsource Hbf Hbs tr).trans
        (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
          Htarget Hbf Hbs tr).symm
    · exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
        Htarget Hbf Hbs

/-!
    [step_sb_any] is [step_sb] with the stored list collapsed from
    [word_to_le_bytes 1 (getr regs rs2)] to its literal singleton byte by
    [SeqExec.N_to_le_bytes_1_small] (the [n = 1] case: this tree's bv model
    stores the low byte directly, so no [< 128] / [< 256] value hypothesis
    is needed).  [step_sb_at] additionally pre-normalizes the store address
    ([Ha]), the stored word ([Hv]) and the stored byte ([Hb]).
    One bridge: both theorems conclude over this file's INLINED [wbytes]
    (the copy of `CatExec.wbytes` carried here until CatExec was wired in),
    while [step_sb] is stated over `CatExec.wbytes`.  The two definitions
    are the same store walk; on a SINGLETON byte list each reduces to the
    same one-byte update, which is what the closing `simp only` uses. -/

/-- [Sb] step lemma with the stored byte exposed exactly as a singleton
    literal ([BitVec.ofInt 8 (getr regs rs2).toNat]). -/
theorem step_sb_any (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          [BitVec.ofInt 8 (getr regs rs2).toNat]) rom) := by
  have hsb := LinuxSem.Common.SeqExec.step_sb segs regs pc mem rom
    w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  rw [LinuxSem.Common.SeqExec.N_to_le_bytes_1_small] at hsb
  rw [hsb]
  simp only [wbytes, LinuxSem.Common.CatExec.wbytes]

/-- [step_sb_any] with the store address and value pre-normalized, and the
    stored byte given as a literal. -/
theorem step_sb_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hv : getr regs rs2 = v)
    (Hb : BitVec.ofInt 8 (v.toNat : Int) = b)
    (Hok : store_ok segs mem a 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom) := by
  have hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 1 = true := by
    rw [Ha]; exact Hok
  rw [step_sb_any segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode hok]
  simp only [Ha, Hv, Hb]


