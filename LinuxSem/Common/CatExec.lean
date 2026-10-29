/-
  * Common.CatExec — image-INDEPENDENT layout / store / to_wexit theory for
    the cat-argv binaries.

  Addresses/pointers are `word = BitVec 64`, bytes are `byte = BitVec 8`,
  register indices are `reg = BitVec 5`.  Purely additive over
  [Common.PropExec] (per-instruction step lemmas, value shapes,
  [rdn]/layout reads) and [Common.CatSim] (the inductive
  [to_wexit]/[msteps]).  Adds:

  - the [ms_read_bytes]->[rdn] bridge ([ms_read_bytes_rdn]);
  - the [wbytes] store theory and the [Sd] step lemma ([step_sd]) needed by
    the target prologue's two stack stores;
  - the argv stack-layout theory ([cat_argv_ptr], [read_argv_ptr_k],
    [read_argv_byte_k], [read_argv_str_k], and the [bsb_*] decompositions);
  - two ergonomic [to_wexit] constructors ([tw_write_gen], [tw_exit0]) and the
    post-svc register collapse [adv_set].  Image-INDEPENDENT.

  Conventions: unbounded address bookkeeping is in [Int] over
  [bv_unsigned] (here `(w.toNat : Int)`); the wrapping [BitVec] address walks
  of [wbytes]/[rdn] carry the (trivially dischargeable) no-overflow side
  conditions mirroring [rdn_stack]/[rdn_ext]; argv-pointer bytes use
  [BvBase.word_le8].

  NOTES.

  - `Section WithFP`'s `Context {fx : FPState}` becomes the ambient
    `variable [fx : FPState]` of the same name, exactly as `PropExec` and
    `MmapSim` do; the section's `fp_regs`/`fp_csr` are `fx.fp_regs`/
    `fx.fp_csr`.
  - `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `Z_to_bv 8 z` is
    `BitVec.ofInt 8 z`, `bv_unsigned w` is `(w.toNat : Int)`,
    `Z.of_nat n` is `(n : Int)`, `bv_signed imm` is `imm.toInt`,
    `bv_eqb a b` is Riscv.Prelude's `bv_eqb`, `length` is `List.length`,
    `firstn`/`skipn` are `List.take`/`List.drop`, `nth k l d` is
    `l[k]?.getD d`, `lia` is `omega`.
  - `decide`-carrying `if`s (`store_ok`, `wrap_mem`'s zero-fill gate,
    CatSim header); the proofs below therefore peel them with `ite_eq_left`/
    `ite_eq_right` (or `ite_eq_right` on a `have`-named negation) rather than `rewrite H`.
  - `Z.of_nat 131071`/`Z.of_nat 2097152` are `((131071 : Nat) : Int)` and
    `((2097152 : Nat) : Int)`: the numerals are already `Int` literals, so
    the `vm_compute`-sealed equations are `rfl` here.
  - `natN_le` is the `N`-comparison restatement  needs for its `N`
    literals; `N` is `Nat` in this tree (`Nat` is the model's index type), so
    the lemma is stated at `Nat` and is the identity.
  helpers, each marked at its declaration.  They exist because of
  two toolchain facts, not because any  statement changed:
  - `omega` in this Lean version gives up on an `Int`-valued SUM compared
    against the literal `2^64` ("no usable constraints found" — a magnitude
    artefact of the tactic).  `int_sum_le_two64` / `nat_sum_le_two64`
    reshape such a bound into one `Nat` cast; `int_sum_le_of_nat` goes back;
    `toNat_add_one` is `u_add1` at `Nat` level. -/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.ExitSim
import LinuxSem.LinuxProcessSem.Sys.Fs.Open
import LinuxSem.LinuxProcessSem.Sys.Fs.Namei
import LinuxSem.LinuxProcessSem.Sys.Uapi

set_option autoImplicit false
-- The same rationale as `PropExec`/`MmapSim`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.CatExec

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.ExitSim
open LinuxSem.LinuxProcessSem.Sys.Fs.Open
open LinuxSem.LinuxProcessSem.Sys.Uapi

section WithFP

variable [fx : FPState]

/- =================================================================
   (A) ms_read_bytes -> rdn bridge
   ================================================================= -/

theorem ms_read_bytes_aux_rdn (segs : List Segment) (ms : machine_state) :
    ∀ (n : Nat) (addr : word),
      ms.ms_rom = seg_rom segs →
      ms_read_bytes_aux ms addr n = rdn segs ms.ms_mem addr n := by
  intro n
  induction n with
  | zero => intro addr _; rfl
  | succ n ih =>
    intro addr Hrom
    simp only [ms_read_bytes_aux, rdn, ms_read_byte, Hrom, seg_rom]
    cases h : ms.ms_mem addr with
    | some b =>
      simp only [h]
      rw [ih (addr + 1) Hrom]
      rfl
    | none =>
      simp only [h]
      cases h2 : memory_read segs addr 1 with
      | none => simp only [h2]
      | some bs =>
        cases bs with
        | nil => simp only [h2]
        | cons b rest =>
          simp only [h2]
          rw [ih (addr + 1) Hrom]
          rfl

theorem ms_read_bytes_rdn (segs : List Segment) (ms : machine_state) (addr len : word)
    (Hrom : ms.ms_rom = seg_rom segs) :
    ms_read_bytes ms addr len = rdn segs ms.ms_mem addr (word_to_nat len) := by
  unfold ms_read_bytes
  exact ms_read_bytes_aux_rdn segs ms (word_to_nat len) addr Hrom

/- =================================================================
   (B) Store-double memory theory
   ================================================================= -/

/-- memory-level mirror of the interpreter's store path (write_to_mem) -/
def wbytes (m : word → Option byte) (addr : word) (bs : List byte) :
    word → Option byte :=
  match bs with
  | [] => m
  | b :: rest =>
    wbytes (fun a => if bv_eqb a addr then some b else m a) (addr + 1) rest

/- (one of two): `omega` in this toolchain gives up on an
    `Int`-valued SUM compared against the literal `2^64` — its preprocessing
    reports "no usable constraints found" for a hypothesis of the shape
    `↑a + ↑b ≤ ↑(2^64)` (a magnitude artefact of the tactic, not a fact about
    the model).  Normalising the sum into ONE `Nat` cast, which it does
    handle, is therefore the first step of every `2^64` bound below; no
     statement is weakened by the reshaping, and the two are
    interchangeable by [Int.natCast_add]. -/
theorem int_sum_le_two64 {a b : Nat}
    (H : (a : Int) + (b : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    ((a + b : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
  rw [Int.natCast_add]; exact H

/-- (two of two): the `Nat`-level reading of the same bound —
    [Int.ofNat_le] of [int_sum_le_two64].  All the address arithmetic below is
    then `Nat` arithmetic (addresses never wrap), with the `Int` view only at
    the statement's boundary. -/
theorem nat_sum_le_two64 {a b : Nat}
    (H : (a : Int) + (b : Int) ≤ ((2 ^ 64 : Nat) : Int)) : a + b ≤ 2 ^ 64 :=
  Int.ofNat_le.mp (int_sum_le_two64 H)

/-- the converse direction, a `Nat` bound lifted to the
    `Int`-sum shape the [rdn] lemmas state their no-overflow side conditions
    in.  (Same reason as [int_sum_le_two64]: the two shapes are the same fact
    written two ways, and only the `Nat` one is `omega`-friendly here.) -/
theorem int_sum_le_of_nat {a b c : Nat} (H : a + b ≤ c) :
    (a : Int) + (b : Int) ≤ (c : Int) := by
  have h : ((a + b : Nat) : Int) ≤ ((c : Nat) : Int) := Int.ofNat_le.mpr H
  rwa [Int.natCast_add] at h

/-- the `Nat` view of [u_add1] (`(a + 1).toNat` when the
    successor does not wrap), so the address arithmetic below can stay in
    `Nat` end to end.  Plain `BitVec` arithmetic: `toNat` of the wrapping add
    is the mod, and the hypothesis turns the mod into the sum. -/
theorem toNat_add_one (a : word) (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1).toNat = a.toNat + 1 := by
  have h1 : ((1 : word)).toNat = 1 := by decide
  rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt h]

/-- Reads at/above the end of the written range are unchanged.  The
    bound [addr + length bs ≤ x < 2^64] already rules out a wrapping
    write walk, so no extra no-overflow hypothesis is needed. -/
theorem wbytes_above (bs : List byte) :
    ∀ (m : word → Option byte) (addr x : word),
      (addr.toNat : Int) + (bs.length : Int) ≤ (x.toNat : Int) →
      wbytes m addr bs x = m x := by
  induction bs with
  | nil => intro m addr x _; rfl
  | cons b rest ih =>
    intro m addr x Hle
    have hlen : (b :: rest).length = rest.length + 1 := rfl
    obtain ⟨_, hx2⟩ := u64_range x
    have hu1 : (addr + 1).toNat = addr.toNat + 1 := toNat_add_one addr (by omega)
    have hne : bv_eqb x addr = false :=
      bv_eqb_neq x addr (by
        intro hc
        have hx' : (x.toNat : Int) = (addr.toNat : Int) := by rw [hc]
        omega)
    have key := ih (fun a => if bv_eqb a addr then some b else m a) (addr + 1) x (by omega)
    have hstep : wbytes m addr (b :: rest)
        = wbytes (fun a => if bv_eqb a addr then some b else m a) (addr + 1) rest := rfl
    rw [hstep, key]
    simp only [hne, Bool.false_eq_true, ite_false]

theorem rdn_wbytes_disjoint (segs : List Segment) (bs : List byte)
    (m : word → Option byte) (addr a : word) (n : Nat)
    (Hle : (addr.toNat : Int) + (bs.length : Int) ≤ (a.toNat : Int))
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  apply rdn_ext
  · exact Hnw
  · intro x Hx
    exact wbytes_above bs m addr x (by omega)

/-- Reads below the written range are unchanged.  A no-overflow
    hypothesis [addr + length bs ≤ 2^64]: the write walk is a wrapping
    [BitVec] add, so without it the tail of a huge write could wrap around
    to [x].  Trivially discharged downstream (stack stores sit far
    below 2^64). -/
theorem wbytes_below (bs : List byte) :
    ∀ (m : word → Option byte) (addr x : word),
      (addr.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      (x.toNat : Int) < (addr.toNat : Int) →
      wbytes m addr bs x = m x := by
  induction bs with
  | nil => intro m addr x _ _; rfl
  | cons b rest ih =>
    --This tree destructs `rest` here: the LAST write of the walk needs no
    -- `u_add1`, and the strict no-overflow bound for `addr + 1` is only
    -- available when at least two bytes remain (as it is for every earlier
    -- step of the walk).
    cases rest with
    | nil =>
      intro m addr x _ _
      have hne : bv_eqb x addr = false :=
        bv_eqb_neq x addr (by
          intro hc
          have hx' : (x.toNat : Int) = (addr.toNat : Int) := by rw [hc]
          omega)
      simp only [wbytes, hne, Bool.false_eq_true, ite_false]
    | cons b' rest' =>
      intro m addr x Hnw Hlt
      have hlen : (b :: b' :: rest').length = rest'.length + 2 := rfl
      have hlen2 : (b' :: rest').length = rest'.length + 1 := rfl
      have hbnd : addr.toNat + (b :: b' :: rest').length ≤ 2 ^ 64 := nat_sum_le_two64 Hnw
      have hne : bv_eqb x addr = false :=
        bv_eqb_neq x addr (by
          intro hc
          have hx' : (x.toNat : Int) = (addr.toNat : Int) := by rw [hc]
          omega)
      have hu1 : (addr + 1).toNat = addr.toNat + 1 := toNat_add_one addr (by omega)
      have hb2 : ((addr + 1).toNat : Int) + ((b' :: rest').length : Int)
          ≤ ((2 ^ 64 : Nat) : Int) := int_sum_le_of_nat (by omega)
      have hlt2 : (x.toNat : Int) < ((addr + 1).toNat : Int) := by omega
      have key := ih (fun a => if bv_eqb a addr then some b else m a) (addr + 1) x hb2 hlt2
      have hstep : wbytes m addr (b :: b' :: rest')
          = wbytes (fun a => if bv_eqb a addr then some b else m a) (addr + 1) (b' :: rest') := rfl
      rw [hstep, key]
      simp only [hne, Bool.false_eq_true, ite_false]

theorem rdn_wbytes_below (segs : List Segment) (bs : List byte)
    (m : word → Option byte) (addr a : word) (n : Nat)
    (Hle : (a.toNat : Int) + (n : Int) ≤ (addr.toNat : Int))
    (Hnw : (addr.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  have _ha := u64_range addr
  apply rdn_ext
  · omega
  · intro x Hx
    exact wbytes_below bs m addr x Hnw (by omega)

/-- The two-sided form.  [rdn_wbytes_disjoint] and [rdn_wbytes_below]
    each need to know WHICH side of the store the read sits on, and a
    peeling tactic has to commit to one of them before its side
    condition is proved.  That is fine for a store at a known address,
    and wrong for a store into an mmap grant: all a proof has about the
    grant base is that it avoids the image ([MmapSim.zfill]'s own
    [rdn_zfill_out] is already stated over exactly this disjunction, for
    the same reason), so neither one-sided bound holds on its own and
    only their disjunction does. -/
theorem rdn_wbytes_out (segs : List Segment) (bs : List byte)
    (m : word → Option byte) (addr a : word) (n : Nat)
    (Hout : (a.toNat : Int) + (n : Int) ≤ (addr.toNat : Int) ∨
      (addr.toNat : Int) + (bs.length : Int) ≤ (a.toNat : Int))
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hnw' : (addr.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wbytes m addr bs) a n = rdn segs m a n := by
  rcases Hout with Hb | Hd
  · exact rdn_wbytes_below segs bs m addr a n Hb Hnw'
  · exact rdn_wbytes_disjoint segs bs m addr a n Hd Hnw

/-- [BvBase] already proves this exact statement; it is restated
    here under this file's namespace so that proof scripts which cite
    `CatExec.length_Z_to_le_bytes`  verbatim. -/
theorem length_Z_to_le_bytes (n : Nat) (z : Int) :
    (Z_to_le_bytes n z).length = n :=
  LinuxSem.LinuxProcessSem.length_Z_to_le_bytes n z

theorem length_N_to_le_bytes (n : Nat) (v : word) :
    (word_to_le_bytes n v).length = n := by
  unfold word_to_le_bytes
  exact length_Z_to_le_bytes n (v.toNat : Int)

/-- The tree interpreter's byte-writer [write_to_mem] IS [wbytes]
    (same recursion, byte [i] at [addr + i]) — the one bridge the
    store-lemma proofs need, since [interp_eff] threads only the
    memory overlay. -/
theorem write_to_mem_wbytes (bs : List byte) :
    ∀ (m : word → Option byte) (addr : word),
      write_to_mem m addr bs = wbytes m addr bs := by
  induction bs with
  | nil => intro m addr; rfl
  | cons b rest ih =>
    intro m addr
    simp only [write_to_mem, wbytes]
    exact ih _ _

/-- Store double: writes 8 bytes to [wbytes] at [rs1+imm]; registers and
    (modulo the store) the rest of memory are unchanged.  The exact stored
    value is irrelevant downstream (only its 8-byte length matters), so it is
    left existential (the witness is [word_to_le_bytes 8 rs2] — the exact
    little-endian byte list the interpreter writes for the tree's
    64-bit [EStore], = [word_le8] of rs2).

    Side-condition: all 8 target bytes must be WRITABLE
    ([RiscvSemantics.store_ok] — present in the overlay, or in a
    segment carrying 'w'), or the store faults.  Note this depends on
    [mem]: a store is bounded by what the process has actually mapped,
    not merely by which segments it misses, so an unmapped-store fault is
    the SIGSEGV it is on Linux and does not silently create a mapping.
    For the stack stores this covers, the target is in the RLIMIT_STACK
    window the initial overlay zero-maps, so the condition closes by
    [Common/StoreOk.solve_store_ok]. -/
theorem step_sd (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store MSize.SZ8 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 8 = true) :
    ∃ bs, bs.length = 8 ∧
      RiscvSemantics.step segs (mkst regs pc mem rom) =
        .MachineOk (mkst regs (v_addi pc 4)
          (wbytes mem (v_addi (getr regs rs1) imm.toInt) bs) rom) := by
  refine ⟨word_to_le_bytes 8 (getr regs rs2), length_N_to_le_bytes 8 _, ?_⟩
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 8 = true := by
    rw [hba]; exact Hok
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, word_to_le_bytes, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/- Below the live stack region the wrapper memory reads as unmapped. -/
theorem stack_max_size_val : stack_max_size = 8388608 := by decide

theorem wrap_mem_below (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (addr : word) (uid hw : word) (rnd : EntryDraw)
    (Hlt : (addr.toNat : Int) < (sp.toNat : Int) - stack_max_size) :
    wrap_mem ph sp argv envp uid hw rnd addr = none := by
  have hsms := stack_max_size_val
  unfold wrap_mem stack_to_mem
  have hsp : ¬ (sp.toNat ≤ addr.toNat) := by omega
  rw [ite_eq_right hsp]
  have hgate : ¬ ((sp.toNat : Int) - stack_max_size ≤ (addr.toNat : Int) &&
      ((addr.toNat : Int) < (sp.toNat : Int))) := by
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  rw [ite_eq_right hgate]


/- =================================================================
   (C) Generic list helpers
   ================================================================= -/

theorem flat_map_app' {A B : Type} (f : A → List B) (l1 l2 : List A) :
    (l1 ++ l2).flatMap f = l1.flatMap f ++ l2.flatMap f :=
  List.flatMap_append

theorem skipn_nth {A : Type} (l : List A) (k : Nat) (d : A) (Hk : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) :=
  List.drop_eq_getElem_cons Hk

/-- `nth k l d` in the `getElem`-with-proof spelling: the bridge between the
    `l[k]?.getD d` this tree writes and the `l[k]'Hk` the list lemmas produce. -/
theorem getElem?_getD_eq {A : Type} (l : List A) (k : Nat) (d : A)
    (Hk : k < l.length) : l[k]?.getD d = l[k]'Hk := by
  rw [List.getElem?_eq_getElem Hk]
  rfl

theorem flat_map_split' {A B : Type} (f : A → List B) (l : List A) (k : Nat)
    (Hk : k < l.length) :
    l.flatMap f = (l.take k).flatMap f ++ f (l[k]'Hk) ++ (l.drop (k + 1)).flatMap f := by
  conv => lhs; rw [← List.take_append_drop k l]
  rw [flat_map_app', skipn_nth l k (l[k]'Hk) Hk, List.flatMap_cons, List.append_assoc]

theorem flat_map_split {A B : Type} (f : A → List B) (l : List A) (k : Nat) (d : A)
    (Hk : k < l.length) :
    l.flatMap f = (l.take k).flatMap f ++ f (l[k]?.getD d) ++ (l.drop (k + 1)).flatMap f := by
  rw [getElem?_getD_eq l k d Hk]
  exact flat_map_split' f l k Hk

theorem flat_map_le8_decomp (l : List word) (k : Nat) (Hk : k < l.length) :
    l.flatMap word_le8 =
      (l.take k).flatMap word_le8 ++ word_le8 (l[k]?.getD (BitVec.ofInt 64 0))
        ++ (l.drop (k + 1)).flatMap word_le8 :=
  flat_map_split word_le8 l k (BitVec.ofInt 64 0) Hk

theorem flatten_strings_decomp (strs : List (List byte)) (k : Nat)
    (Hk : k < strs.length) :
    flatten_strings strs =
      flatten_strings (strs.take k)
        ++ (strs[k]?.getD [] ++ [BitVec.ofInt 8 0])
        ++ flatten_strings (strs.drop (k + 1)) :=
  flat_map_split (fun s => s ++ [BitVec.ofInt 8 0]) strs k [] Hk

theorem total_arg_bytes_cons (s : List byte) (l : List (List byte)) :
    total_arg_bytes_nat (s :: l) = s.length + 1 + total_arg_bytes_nat l := rfl

theorem total_arg_bytes_firstn_le (k : Nat) : ∀ l : List (List byte),
    total_arg_bytes_nat (l.take k) ≤ total_arg_bytes_nat l := by
  induction k with
  | zero => intro l; exact Nat.zero_le _
  | succ k ih =>
    intro l
    cases l with
    | nil => exact Nat.zero_le _
    | cons s rest =>
      rw [List.take_succ_cons, total_arg_bytes_cons, total_arg_bytes_cons]
      have := ih rest
      omega

/--This tree states this for `N` (`N.of_nat n <= N.of_nat m`); `N`
    is `Nat` in this tree (`Nat` is the model's index type everywhere), so the
    statement is the identity — kept as its own name because the
    proof scripts cite it. -/
theorem natN_le {n m : Nat} (h : n ≤ m) : n ≤ m := h

/-- `vm`-computed equations for `Z.of_nat` on the two large literals from
    [valid_argv]; sealing them behind a [Qed] keeps the (expensive) lazy
    conversion through a multi-million-cell unary `nat` out of both the
    tactic and the Qed-time kernel check of every user of these bounds.

    `Z.of_nat n` is `((n : Nat) : Int)` here, and a `Nat` literal
    coerces to the corresponding `Int` literal by computation, so the
     `vm_compute; reflexivity` is `rfl`. -/
theorem of_nat_131071 : ((131071 : Nat) : Int) = 131071 := rfl
theorem of_nat_2097152 : ((2097152 : Nat) : Int) = 2097152 := rfl

/- =================================================================
   (D) Cat-argv stack-layout abbreviations
   ================================================================= -/

def cat_struct_size (av ev : List (List byte)) : Nat :=
  8 + (av.length + 1) * 8 + (ev.length + 1) * 8 + auxv_size  -- auxv_size = length auxv_bytes

def cat_string_base (sp : word) (av ev : List (List byte)) : word :=
  sp + nat_to_word (cat_struct_size av ev)

def cat_env_base (sp : word) (av ev : List (List byte)) : word :=
  cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av)

/-- The k-th argv pointer value: the address of argv string k's bytes. -/
def cat_argv_ptr (sp : word) (av ev : List (List byte)) (k : Nat) : word :=
  ((string_addrs (cat_string_base sp av ev) av).1[k]?).getD (BitVec.ofInt 64 0)

theorem nth_string_addrs (strs : List (List byte)) :
    ∀ (base : word) (k : Nat), k < strs.length →
      ((string_addrs base strs).1[k]?).getD (BitVec.ofInt 64 0)
        = base + nat_to_word (total_arg_bytes_nat (strs.take k)) := by
  induction strs with
  | nil => intro base k Hk; simp at Hk
  | cons s rest ih =>
    intro base k Hk
    rw [string_addrs_fst_structure]
    cases k with
    | zero =>
      have h1 : (s :: rest).take 0 = [] := rfl
      have h2 : total_arg_bytes_nat ([] : List (List byte)) = 0 := rfl
      rw [h1, h2, word_add_0]
      rfl
    | succ k' =>
      have h1 : (s :: rest).take (k' + 1) = s :: rest.take k' := rfl
      rw [h1, total_arg_bytes_cons, List.getElem?_cons_succ]
      rw [ih (base + len_word s + 1) k' (by
        simp only [List.length_cons] at Hk; omega)]
      rw [len_word_nat, word1_nat, nat_to_word_add_merge base s.length 1,
        nat_to_word_add_merge base (s.length + 1)]

theorem cat_argv_ptr_offset (sp : word) (av ev : List (List byte)) (k : Nat)
    (Hk : k < av.length) :
    cat_argv_ptr sp av ev k
      = cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat (av.take k)) := by
  unfold cat_argv_ptr
  exact nth_string_addrs av (cat_string_base sp av ev) k Hk


/- =================================================================
   (E) build_stack_bytes decompositions
   ================================================================= -/

/-- The fixed-size struct prefix that precedes the string data. -/
def cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) : List byte :=
  word_le8 (len_word av)
  ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8
  ++ word_le8 (BitVec.ofInt 64 0)
  ++ (string_addrs (cat_env_base sp av ev) ev).1.flatMap word_le8
  ++ word_le8 (BitVec.ofInt 64 0) ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw

theorem length_cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) :
    (cat_struct_prefix ph sp av ev uid hw).length = cat_struct_size av ev := by
  unfold cat_struct_prefix cat_struct_size
  simp only [List.length_append, length_flat_map_le8, length_string_addrs_fst, length_n_to_le_8,
    length_auxv_bytes]
  omega

/-- build = argc ++ argv_ptrs ++ <tail>. -/
theorem bsb_argv_prefix (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ∃ tail, build_stack_bytes ph sp av ev uid hw rnd =
      word_le8 (len_word av)
        ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8 ++ tail := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    unfold build_stack_bytes cat_string_base cat_struct_size
    simp only []
    rw [length_auxv_bytes, string_addrs_pair av, string_addrs_pair ev]
    simp only [List.append_assoc]
    rfl


/-- build = (argc ++ argv_ptrs[<k]) ++ argv_ptrs[k] ++ <post>. -/
theorem bsb_ptr_k (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (k : Nat)
    (uid hw : word) (rnd : EntryDraw) (Hk : k < av.length) :
    ∃ post, build_stack_bytes ph sp av ev uid hw rnd =
      (word_le8 (len_word av)
        ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8)
      ++ word_le8 (((string_addrs (cat_string_base sp av ev) av).1[k]?).getD (BitVec.ofInt 64 0))
      ++ post := by
  obtain ⟨tail, E⟩ := bsb_argv_prefix ph sp av ev uid hw rnd
  have Hk' : k < (string_addrs (cat_string_base sp av ev) av).1.length := by
    rw [length_string_addrs_fst]; exact Hk
  rw [flat_map_le8_decomp _ k Hk'] at E
  refine ⟨?_, ?_⟩
  case refine_2 =>
    rw [E]
    simp only [List.append_assoc]
    rfl

theorem read_argv_ptr_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (Hk : k < av.length)
    (Hnw : (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int)
      < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (sp + nat_to_word (8 + 8 * k)) 8
      = some (word_le8 (cat_argv_ptr sp av ev k)) := by
  obtain ⟨post, E⟩ := bsb_ptr_k ph sp av ev k uid hw rnd Hk
  have H' := read_at_offset_image segs ph sp av ev uid hw rnd
    (word_le8 (len_word av)
      ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8)
    (word_le8 (((string_addrs (cat_string_base sp av ev) av).1[k]?).getD (BitVec.ofInt 64 0)))
    post 8 E (length_n_to_le_8 _) Hnw
  have Hlen : (word_le8 (len_word av)
      ++ ((string_addrs (cat_string_base sp av ev) av).1.take k).flatMap word_le8).length
      = 8 + 8 * k := by
    rw [List.length_append, length_n_to_le_8, length_flat_map_le8, List.length_take,
      length_string_addrs_fst, Nat.min_eq_left (by omega)]
  rw [Hlen] at H'
  rw [H']
  unfold cat_argv_ptr
  rfl

/-- build = <pre> ++ (argv[k] ++ [0]) ++ <post>, with [length pre] known. -/
theorem bsb_strings_split (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ∃ tail, build_stack_bytes ph sp av ev uid hw rnd
      = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    unfold build_stack_bytes cat_struct_prefix cat_env_base cat_string_base
    simp only []
    rw [length_auxv_bytes, string_addrs_pair av, string_addrs_pair ev]
    simp only [List.append_assoc]
    rfl

theorem bsb_byte_k (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (k : Nat)
    (uid hw : word) (rnd : EntryDraw) (Hk : k < av.length) :
    ∃ pre post, build_stack_bytes ph sp av ev uid hw rnd
        = pre ++ (av[k]?.getD [] ++ [BitVec.ofInt 8 0]) ++ post
      ∧ pre.length = cat_struct_size av ev + total_arg_bytes_nat (av.take k) := by
  obtain ⟨tail, E⟩ := bsb_strings_split ph sp av ev uid hw rnd
  rw [flatten_strings_decomp av k Hk] at E
  refine ⟨cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (av.take k), ?_, ?_⟩
  case refine_2 =>
    refine ⟨?_, ?_⟩
    · rw [E]
      simp only [List.append_assoc]
      rfl
    · rw [List.length_append, length_cat_struct_prefix, length_flatten_strings]


theorem read_argv_byte_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k j : Nat) (uid hw : word) (rnd : EntryDraw)
    (Hk : k < av.length) (Hj : j ≤ (av[k]?.getD []).length)
    (Hnw : (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int)
      < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k + nat_to_word j) 1
      = some [(av[k]?.getD [] ++ [BitVec.ofInt 8 0])[j]?.getD (BitVec.ofInt 8 0)] := by
  obtain ⟨pre, post, E, Hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd Hk
  have H' := read_byte_at_image segs ph sp av ev uid hw rnd
    pre (av[k]?.getD [] ++ [BitVec.ofInt 8 0]) post j E
  rw [Hlen] at H'
  have hptr : cat_argv_ptr sp av ev k + nat_to_word j
      = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k) + j) := by
    rw [cat_argv_ptr_offset sp av ev k Hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge, nat_to_word_add_merge, ← Nat.add_assoc]
  rw [hptr]
  exact H' (by rw [List.length_append, List.length_singleton]; omega) Hnw

theorem read_argv_str_k (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (k : Nat) (uid hw : word) (rnd : EntryDraw)
    (Hk : k < av.length)
    (Hnw : (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int)
      < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
        (cat_argv_ptr sp av ev k) (av[k]?.getD []).length
      = some (av[k]?.getD []) := by
  obtain ⟨pre, post, E, Hlen⟩ := bsb_byte_k ph sp av ev k uid hw rnd Hk
  have H' := read_at_offset_image segs ph sp av ev uid hw rnd
    pre (av[k]?.getD []) ([BitVec.ofInt 8 0] ++ post) (av[k]?.getD []).length
  rw [Hlen] at H'
  have hptr : cat_argv_ptr sp av ev k
      = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k Hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge]
  rw [hptr]
  exact H' (by rw [E]; simp only [List.append_assoc]) rfl Hnw

/- =================================================================
   (E.5) [byte_at] unpacking and [valid_argv] projections

   [byte_at s k] is the NUL-padded k-th byte of [s] (the byte an argv
   string reads back as at offset [k], including the implicit
   terminating NUL at [k = length s]).  Every example that walks an
   argv string byte-by-byte defined this identically; centralized
   here next to the argv layout theory it decomposes.
   ================================================================= -/

/-- `nth` in this tree's spelling: `l[k]?.getD d`. -/
def byte_at (s : List byte) (k : Nat) : byte :=
  (s ++ [BitVec.ofInt 8 0])[k]?.getD (BitVec.ofInt 8 0)

theorem nth_lt_byte_at (s : List byte) (j : Nat) (Hj : j < s.length) :
    byte_at s j = s[j]'Hj := by
  unfold byte_at
  rw [List.getElem?_append_left Hj, List.getElem?_eq_getElem Hj]
  rfl

theorem byte_at_len (s : List byte) : byte_at s s.length = BitVec.ofInt 8 0 := by
  unfold byte_at
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem byte_at_nz (s : List byte) (j : Nat) (Hnz : BitVec.ofInt 8 0 ∉ s)
    (Hj : j < s.length) : byte_at s j ≠ BitVec.ofInt 8 0 := by
  intro Hc
  apply Hnz
  rw [← Hc, nth_lt_byte_at s j Hj]
  exact List.getElem_mem Hj

/-- Bytes are typed, so the bound holds hypothesis-free. -/
theorem byte_at_bound (s : List byte) (j : Nat) : ((byte_at s j).toNat : Int) < 256 := by
  unfold byte_at
  have := nth_app0_bound s j
  omega

theorem valid_argv_len (av : List (List byte)) (H : valid_argv av) :
    (av.length : Int) ≤ 1024 := by
  unfold valid_argv at H
  exact H.1.2

theorem valid_argv_nonempty (av : List (List byte)) (H : valid_argv av) :
    1 ≤ av.length := by
  unfold valid_argv at H
  have h1 : (1 : Int) ≤ (av.length : Int) := H.1.1
  exact Int.ofNat_le.mp h1

theorem valid_argv_str_len (av : List (List byte)) (k : Nat) (H : valid_argv av)
    (Hk : k < av.length) : ((av[k]?.getD []).length : Int) ≤ 131071 := by
  unfold valid_argv at H
  have hstr : ∀ a ∈ av, (a.length : Int) ≤ 131071 := H.2.2.1
  rw [getElem?_getD_eq av k [] Hk]
  exact hstr _ (List.getElem_mem Hk)

theorem valid_argv_str_nz (av : List (List byte)) (k : Nat) (H : valid_argv av)
    (Hk : k < av.length) : BitVec.ofInt 8 0 ∉ av[k]?.getD [] := by
  unfold valid_argv at H
  have hnz : ∀ a ∈ av, BitVec.ofInt 8 0 ∉ a := H.2.2.2.1
  rw [getElem?_getD_eq av k [] Hk]
  exact hnz _ (List.getElem_mem Hk)

/-- The fifth [valid_argv] clause, delivered in the shape
    [Sys.Fs.Open]'s arms ask for.

    THE INDEX IS [S k] BECAUSE THE CLAUSE IS ON THE TAIL: argv[0]
    conventionally holds a path, so [Run.valid_argv] says nothing about
    it and this lemma cannot either.  Both callers open [nth 1] and
    [nth 2], which is why the tail is enough.

    The [dot_path] side is NOT supplied here: "." is a path the model
    resolves, so whether an argument is "." is a case the caller splits
    on rather than a validity question — which is exactly how
    [Examples.cp_ns] and [Examples.headcp_ns] reach this lemma, with the
    false branch of their own split in hand. -/
theorem valid_argv_str_plain (av : List (List byte)) (k : Nat) (H : valid_argv av)
    (Hk : k + 1 < av.length)
    (Hdot : Fs.path_eqb (av[k + 1]?.getD []) dot_path = false) :
    openat_plain_name (av[k + 1]?.getD []) = true := by
  unfold valid_argv at H
  have Hpl : ∀ a ∈ av.tail, Sys.Fs.Namei.path_has_slash a = false
      ∧ Fs.path_eqb a Sys.Fs.Namei.dotdot_path = false := H.2.2.2.2
  have Hk' : k < av.tail.length := by
    cases av with
    | nil => simp at Hk
    | cons a av' => simp only [List.length_tail]; omega
  have Hmem : (av.tail[k]?.getD []) ∈ av.tail := by
    rw [getElem?_getD_eq _ _ _ Hk']
    exact List.getElem_mem Hk'
  obtain ⟨Hsl, Hdd⟩ := Hpl _ Hmem
  -- [Run.valid_argv] spells the two tests with `Sys.Fs.Namei`'s constants and
  -- `openat_plain_name`/`path_is_dirref` with `Sys.Fs.Open`'s; the two pairs
  -- are definitionally the same bytes (both files pin their separator and
  -- their `..` to the same literals), so the restatements are `rfl`.
  have Hsl' : Sys.Fs.Open.path_has_slash (av.tail[k]?.getD []) = false := Hsl
  have Hdd' : Fs.path_eqb (av.tail[k]?.getD []) Sys.Fs.Open.dotdot_path = false := Hdd
  have Hnth : (av[k + 1]?.getD []) = (av.tail[k]?.getD []) := by
    cases av with
    | nil => simp at Hk
    | cons a av' => rfl
  rw [Hnth] at Hdot ⊢
  unfold openat_plain_name path_is_dirref
  simp only [Hdot, Hdd', Hsl', Bool.or_false, Bool.not_false, Bool.true_and]

/-- Trivial since bytes are typed; kept as the restatement so
    downstream call sites survive. -/
theorem valid_argv_str_bytes (av : List (List byte)) (k : Nat) (_ : valid_argv av)
    (Hk : k < av.length) : ∀ b ∈ av[k]?.getD [], ((b.toNat : Int) < 256) := by
  intro b _
  exact (u8_range b).2

/- =================================================================
   (F) Extra value facts used by the target binary
   ================================================================= -/

/-- Hypothesis-free: the wrap in [BitVec.ofInt] cancels.  [x + 1] is the
    wrapping [BitVec] add, convertible with [v_addi x 1]. -/
theorem v_addi_pred (x : word) : v_addi (x + 1) (-1) = x := by
  unfold v_addi
  by_cases h : x.toNat + 1 < 2 ^ 64
  · have ht : (x + 1).toNat = x.toNat + 1 := toNat_add_one x h
    rw [ht]
    have hc : ((x.toNat + 1 : Nat) : Int) + (-1) = (x.toNat : Int) := by
      rw [Int.natCast_add]
      omega
    rw [hc, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have hx : x.toNat = 2 ^ 64 - 1 := by have := x.isLt; omega
    have ht : (x + 1).toNat = 0 := by
      rw [BitVec.toNat_add, show ((1 : word)).toNat = 1 from by decide, hx,
        show 2 ^ 64 - 1 + 1 = 2 ^ 64 from by omega, Nat.mod_self]
    rw [ht]
    have hc : ((0 : Nat) : Int) + (-1) = (-1 : Int) := by omega
    rw [hc]
    have hneg : (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 := by decide
    apply BitVec.eq_of_toNat_eq
    rw [hx, hneg]


/- =================================================================
   (G) Ergonomic [to_wexit] constructors

   A plain run of instructions is an [msteps] (chained from
   [PropExec.step_*] via [CatSim.msteps_to_wexit]); a write is
   [tw_write] with its post-svc register file collapsed by [adv_set];
   a code-0 exit is [tw_exit0].
   ================================================================= -/

/-- The pending state a write/exit syscall dispatches from. -/
def pend (regs : BvMap word) (pc : word) (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
    ms_svc_pending := some (BitVec.ofInt 64 64), ms_resv := none, ms_fcsr := fx.fp_csr,
    ms_mem := mem, ms_rom := rom }

/-- Collapse [advance_past_svc (set_gpr0 <record> v)] to a [mkst]: advance the
    PC past the svc after writing the (dead) syscall return to x10. -/
theorem adv_set (regs : BvMap word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (v : word) :
    advance_past_svc (set_gpr0
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom } v)
      = mkst (regupd regs 10 v) (v_addi pc 4) mem rom := by
  have hne : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, set_gpr0, set_reg, hne, Bool.false_eq_true, ite_false,
    reduceIte, ms_pc, mkst, regupd, b_npc4]

/-- A write to fd 1 at a [pend] state, continuing with the post-svc state.
    The environment may deliver any nonempty prefix of [buf], so the
    continuation is the delivered-length family: x10 holds
    [len_word (firstn n buf)] for the chosen [n]. -/
theorem tw_write_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (buf : List byte) (bufs : List (List byte)) (code : word)
    (Hg0 : ms_gpr (pend regs pc mem rom) 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes (pend regs pc mem rom)
      (ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
       to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n)))
         (v_addi pc 4) mem rom) bufs code) :
    to_wexit segs (pend regs pc mem rom) (buf :: bufs) code := by
  refine to_wexit.tw_write (segs := segs) (pend regs pc mem rom) (BitVec.ofInt 64 64)
    buf bufs code rfl ?_ Hg0 Hr Hnb ?_
  · decide
  · intro n Hn1 Hn2
    have hstep : advance_past_svc (set_gpr0 (pend regs pc mem rom) (len_word (buf.take n)))
        = mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom := by
      unfold pend
      exact adv_set regs pc _ mem rom _
    rw [hstep]
    exact Hcont n Hn1 Hn2

/-- A [code]-0 exit: the pending state carries an exit syscall number and a0 = 0. -/
theorem tw_exit0 (segs : List Segment) (ms : machine_state) (x8 : word)
    (Hsvc : ms.ms_svc_pending = some x8) (Hex : is_exit_no x8)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) :
    to_wexit segs ms [] (BitVec.ofInt 64 0) := by
  have hc : ms_gpr ms 0 &&& BitVec.ofInt 64 255 = BitVec.ofInt 64 0 := by
    rw [Hg0]; decide
  rw [← hc]
  exact to_wexit.tw_exit ms x8 Hsvc Hex

/-- A write at the raw ecall post-state record (svc field is [some (getr regs
    17)], as [step_ecall] leaves it).  [reg_get regs 10/11/12] are a0/a1/a2.
    The syscall-number test is Int-characterized, mirroring [tw_write]. -/
theorem tw_write_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (buf : List byte) (bufs : List (List byte)) (code : word)
    (H17 : ((getr regs 17).toNat : Int) = 64)
    (H10 : reg_get regs 10 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
       to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n)))
         (v_addi pc 4) mem rom) bufs code) :
    to_wexit segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      (buf :: bufs) code := by
  refine to_wexit.tw_write (segs := segs)
    { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
      ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
      ms_mem := mem, ms_rom := rom }
    (getr regs 17) buf bufs code rfl H17 ?_ ?_ Hnb ?_
  · simp only [ms_gpr, arg_reg_0]
    exact H10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]
    exact Hr
  · intro n Hn1 Hn2
    have hstep : advance_past_svc (set_gpr0
        { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
          ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
          ms_mem := mem, ms_rom := rom } (len_word (buf.take n)))
        = mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom :=
      adv_set regs pc _ mem rom _
    rw [hstep]
    exact Hcont n Hn1 Hn2

/-- A code-0 exit at the raw ecall post-state record ([a7 = 93], a0 = 0). -/
theorem tw_exit_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (H17 : ((getr regs 17).toNat : Int) = 93)
    (H10 : reg_get regs 10 = BitVec.ofInt 64 0) :
    to_wexit segs
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom } [] (BitVec.ofInt 64 0) := by
  refine tw_exit0 segs _ (getr regs 17) rfl (Or.inl H17) ?_
  simp only [ms_gpr, arg_reg_0]
  exact H10

end WithFP

section Sanity

/-- Sanity check for [byte_at]: in range it is the byte. -/
example : byte_at [BitVec.ofInt 8 65, BitVec.ofInt 8 66] 0 = BitVec.ofInt 8 65 := by decide

/-- Sanity check for [byte_at]: at the string's length it is the implicit
    terminating NUL. -/
example : byte_at [BitVec.ofInt 8 65, BitVec.ofInt 8 66] 2 = BitVec.ofInt 8 0 := by decide

/-- Sanity check for [cat_struct_size] on an empty argv/envp: the argc word,
    one argv NULL, one envp NULL, and the 160-byte auxv. -/
example : cat_struct_size [] [] = 184 := by decide

/-- Sanity check for [cat_argv_ptr]: an empty argv has no pointer, so the
    default (a null word) is what reads back. -/
example : cat_argv_ptr (BitVec.ofInt 64 1000) [] [] 0 = BitVec.ofInt 64 0 := by decide

/-- Sanity check for [v_addi_pred] at a concrete word. -/
example : v_addi (BitVec.ofInt 64 41 + 1) (-1) = BitVec.ofInt 64 41 := by decide

end Sanity


