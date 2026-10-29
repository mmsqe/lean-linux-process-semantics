/-
  * Common.ArgvEnv — parametric argv/envp/stack-window startup scaffolding

  Every example's source/target proof rebuilds the same startup
  bookkeeping out of only the initial stack pointer [sp], the argv/envp
  lists [av]/[ev], and the four ambient hypotheses shared by every
  binary ([valid_argv av], [valid_envp ev] and the OS-fixed sp-window
  bounds).  This module proves that bookkeeping ONCE, in a section
  quantified over [(segs, sp, av, ev)] plus those four hypotheses, so a
  per-binary file instantiates it (twice: once at the source [rsp], once
  at the target [asp]) with a one-line [exact]/[apply] per lemma instead
  of re-deriving it.

  What lives here (fully determined by [sp], [av], [ev] and the
  hypotheses, so it generalizes cleanly):

  - [sp_lo_num]/[sp_hi_num] : the OS sp-window restated as raw hex
    bounds (the [rsp_lo_num]/[rsp_hi_num] / [asp_*] twins);
  - [argcN] / [u_argcN]     : the argument count as a [word];
  - [bsb_nw]                : the initial stack image fits under 2^64
    (the [source_bsb_nw] / [target_bsb_nw] no-overflow side condition);
  - [envp_ptr] / [envp_ptr_eq] : musl's [environ] pointer and the fact
    that _start's [addi (add sp<<...) 8] computes it;
  - [wmem] / [rdn_wmem_stack] / [read_argc_w] : the initial wrapped
    memory, its agreement with the raw stack image at/above [sp], and
    the read-back of the [argc] word;
  - [argv_ptr_bounds_at] / [read_argv_ptr_w] : the [k]-th argv pointer's
    address bounds and its read-back through [wmem] (via CatExec's
    [cat_argv_ptr] / [read_argv_ptr_k]).

  What CANNOT live here (depends on the per-binary memory OVERLAY — the
  example's [fmem]/[emem] wbytes stack of callee-save/environ stores —
  or on FileSim, which not every example imports): the
  [rdn_<overlay>_above] peel lemmas and the overlay-level argv read-back
  lemmas ([read_psrc_*], [source_cstr_*]).  Those stay local; their
  generic tail is exactly [rdn_wmem_stack] + [read_argv_ptr_w] /
  FileSim's [read_argv_cstr_k], which they call after peeling their own
  overlay down to [wmem].

  This file imports only Common (up to StepTac) and the specification;
  it never imports an example.

  Reference instantiation: [Examples/modprint_ns/modprint_ns_source]
  and [..._target] (the [rsp] and [asp] copies).  Some other examples
  hand-roll the same lemmas; new examples should not.

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  * The  `Section Scaffold` variables become EXPLICIT parameters,
    in the order ([segs], [ph], [sp], [av], [ev], [uid], [hw],
    [rnd], then the hypotheses [Hva], [Hve], [Hsp_lo], [Hsp_hi]).  Each
    declaration carries only the variables/hypotheses it actually uses,
    exactly as a Lean section would abstract them; a call site writes
    `envp_ptr_eq sp av Hva Hsp_lo Hsp_hi` — the binders are explicit, so no
    section-variable insertion is relied on.
 Nothing here inspects [fx].
  * `Z` → `Int`, `bv_unsigned w` → `(w.toNat : Int)`,
    `Z.of_nat (length l)` → `(l.length : Int)`, `Z_to_bv n z` →
    `BitVec.ofInt n z`, `nth k av []` → `av[k]?.getD []`, `2^64` (over
    `Z`) → `((2 ^ 64 : Nat) : Int)`.
  * [sp_lo_num]/[sp_hi_num] stay stated at the raw hex literals (that is
    their point: they are the numeric twins the per-binary files use);
    they are proved by unfolding [sp_window_lo]/[sp_window_hi], which are
    transparent, so the proof is the hypothesis itself.
  * [u_argcN]: `bv_unsigned argcN = Z.of_nat (length av)`.  In Lean the identity is a
    plain mod-2^64 congruence: both sides are
    `BitVec.ofInt 64 (…)` and the only difference is
    `argcN.toNat * 2^3` vs `8 * av.length`, so
    `BitVec.eq_of_toNat_eq` + [BitVec.toNat_ofInt] + `omega` closes it
    without any sp-window hypothesis.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac

namespace LinuxSem.Common.ArgvEnv

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac

section Scaffold

/-! The loaded segments (source_segs / target_segs at each call site), the
    initial (ASLR-quantified) stack pointer, and the argv/envp lists, the
    image's program-header record ([MemImageType.PhdrInfo]: the auxv carries
    it, so the initial stack image depends on it), the process's uid, the
    AT_HWCAP word, and the run's AT_RANDOM draw (the [ed_random] half of
    [Run.ExecEntry]'s [en_draw]: the last 16 bytes of the initial stack
    image and nothing else, so no lemma in this section constrains it) are
    all EXPLICIT parameters below, in this order.  The four ambient
    hypotheses every binary shares are [Hva], [Hve], [Hsp_lo] and
    [Hsp_hi]. -/

variable [fx : FPState]

/-! ## sp-window bounds (the [rsp_lo_num]/[rsp_hi_num] / [asp_*] twins) -/

/-- The OS sp-window floor, restated as the raw hex bound the per-binary
    files state their [rsp_lo_num]/[asp_lo_num] twins at. -/
theorem sp_lo_num (sp : word) (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int)) :
    (0x7fff80000000 : Int) ≤ (sp.toNat : Int) :=
  Hsp_lo

/-- The OS sp-window ceiling, restated as the raw hex bound (see
    [sp_lo_num]). -/
theorem sp_hi_num (sp : word) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    (sp.toNat : Int) ≤ (0x800000000000 : Int) :=
  Hsp_hi

/-! ## argc -/

/-- The argument count as a [word]. -/
def argcN (av : List (List byte)) : word := len_word av

/-- [bv_unsigned] of [argcN]: `bv_unsigned argcN = Z.of_nat (length av)`.
-/
theorem u_argcN (av : List (List byte)) (Hva : valid_argv av) :
    ((argcN av).toNat : Int) = (av.length : Int) := by
  have hlen : (av.length : Int) ≤ 1024 := valid_argv_len av Hva
  unfold argcN len_word
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## No-overflow bound for the initial stack image -/

/-- The whole initial stack image sits below `2^64`: the [source_bsb_nw] /
    [target_bsb_nw] no-overflow side condition every read lemma asks for.
-/
theorem bsb_nw (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    (sp.toNat : Int)
      + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < ((2 ^ 64 : Nat) : Int) := by
  have h1 := bsb_bound ph sp av ev uid hw rnd Hva Hve
  have h2 := sp_hi_num sp Hsp_hi
  omega

/-! ## envp pointer (the value _start stores into musl's environ slot) -/

/-- musl's [environ] slot value: the address of the envp pointer array,
    `sp + 8` (argc) `+ 8 * argc` (the argv pointers) `+ 8` (argv's NULL
    terminator). -/
def envp_ptr (sp : word) (av : List (List byte)) : word :=
  BitVec.ofInt 64 ((sp.toNat : Int) + 8 + 8 * (av.length : Int) + 8)

/-- `_start`'s `addi (add (add sp 8) (slli argc 3)) 8` computes musl's
    [environ] pointer ([envp_ptr]).

    see the module header — Lean proves the mod-2^64 congruence
    directly, so the statement needs no sp-window hypothesis. -/
theorem envp_ptr_eq (sp : word) (av : List (List byte)) (Hva : valid_argv av) :
    v_addi (v_add (BitVec.ofInt 64 ((sp.toNat : Int) + 8)) (v_slli (argcN av) 3)) 8
      = envp_ptr sp av := by
  have hlen : (av.length : Int) ≤ 1024 := valid_argv_len av Hva
  have hargc : ((argcN av).toNat : Int) = (av.length : Int) := u_argcN av Hva
  unfold envp_ptr v_addi v_add v_slli zshiftl
  rw [hargc]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Int.reduceToNat]
  omega

/-! ## Wrapped initial memory and its read-backs -/

/-- The initial wrapped memory (`init_machine_state`'s overlay). -/
def wmem (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rnd : EntryDraw) : word → Option byte :=
  wrap_mem ph sp av ev uid hw rnd

/-- At/above [sp] the wrapper equals the raw stack image (peels the
    zero-fill branch); this is the shared, overlay-free member of the
    [rdn_<layer>_above]/[rdn_wmem_stack] peeling triad. -/
theorem rdn_wmem_stack (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw) (a : word) (n : Nat)
    (Ha : (sp.toNat : Int) ≤ (a.toNat : Int))
    (Hn : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wmem ph sp av ev uid hw rnd) a n
      = rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) a n :=
  rdn_wrap_stack_above segs ph sp av ev a n uid hw rnd Ha Hn

/-- The argc word at [sp]. -/
theorem read_argc_w (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (Hva : valid_argv av) (Hve : valid_envp ev) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    rdn segs (wmem ph sp av ev uid hw rnd) sp 8 = some (word_le8 (argcN av)) := by
  have hbsb := bsb_nw ph sp av ev uid hw rnd Hva Hve Hsp_hi
  have h8 : (sp.toNat : Int) + ((8 : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    have h2 := sp_hi_num sp Hsp_hi
    omega
  rw [rdn_wmem_stack segs ph sp av ev uid hw rnd sp 8 (Int.le_refl _) h8]
  exact read_argc ph segs sp av ev uid hw rnd hbsb

/-! ## argv-pointer group (pointer bounds + read-back of the pointer word
    through [wmem]) -/

/-- Address bounds for the [k]-th argv pointer.  Generalizes the
    per-example [psrc_bounds]/[pdst_bounds] over the index [k]; note it is
    [segs]- and overlay-independent.
-/
theorem argv_ptr_bounds_at (sp : word) (av ev : List (List byte))
    (Hva : valid_argv av) (Hve : valid_envp ev) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < av.length) :
    ((sp.toNat : Int) ≤ ((cat_argv_ptr sp av ev k).toNat : Int)) ∧
    (((cat_argv_ptr sp av ev k).toNat : Int)
      + (((av[k]?.getD []).length : Nat) : Int) + 1 < ((2 ^ 64 : Nat) : Int)) := by
  have hsp : (sp.toNat : Int) + argv_layout_slack < ((2 ^ 64 : Nat) : Int) := by
    have h2 := sp_hi_num sp Hsp_hi
    unfold argv_layout_slack
    omega
  exact argv_ptr_bounds sp av ev k Hva Hve Hk hsp

/-- Read-back of the [k]-th argv pointer word out of [wmem] (the overlay-free
    tail the [read_psrc_*]/[read_pdst_*] lemmas reduce to after peeling
    their own overlay). -/
theorem read_argv_ptr_w (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (Hva : valid_argv av) (Hve : valid_envp ev) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < av.length) :
    rdn segs (wmem ph sp av ev uid hw rnd) (sp + nat_to_word (8 + 8 * k)) 8
      = some (word_le8 (cat_argv_ptr sp av ev k)) := by
  have hbsb := bsb_nw ph sp av ev uid hw rnd Hva Hve Hsp_hi
  have hlen : (av.length : Int) ≤ 1024 := valid_argv_len av Hva
  -- the sp-window top as a NUMERAL: [omega] needs it in the outer context,
  -- not inside a sub-proof, or the ceiling stays an opaque atom
  have hspTop : (sp.toNat : Int) ≤ 0x800000000000 := Hsp_hi
  have hspN : sp.toNat + (8 + 8 * k) < 2 ^ 64 := by omega
  have hto : (sp + nat_to_word (8 + 8 * k)).toNat = sp.toNat + (8 + 8 * k) :=
    toNat_add_nat_to_word sp (8 + 8 * k) hspN
  have hlo : (sp.toNat : Int) ≤ ((sp + nat_to_word (8 + 8 * k)).toNat : Int) := by
    rw [hto]; omega
  have hhi : ((sp + nat_to_word (8 + 8 * k)).toNat : Int)
      + ((8 : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hto]; omega
  rw [rdn_wmem_stack segs ph sp av ev uid hw rnd (sp + nat_to_word (8 + 8 * k)) 8 hlo hhi]
  exact read_argv_ptr_k ph segs sp av ev k uid hw rnd Hk hbsb

end Scaffold

/-! -/

example : argcN [[1], [2], [3]] = BitVec.ofInt 64 3 := by decide
example : ((argcN [[1], [2], [3]]).toNat : Int) = 3 := by decide
example : argcN ([] : List (List byte)) = BitVec.ofInt 64 0 := by decide
