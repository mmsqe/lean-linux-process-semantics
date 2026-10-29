/-
  * Common.RefLayout — initial-stack layout read-backs beyond argv:
    the argv NULL, the envp pointer slots and their NULL, the 20 auxv
    words, and the 16-byte AT_RANDOM block.

  Image-INDEPENDENT (a section over [segs ph sp av ev] with the four
  ambient hypotheses, like [ArgvEnv]).  Companion of
  [PropExec.read_argc] / [CatExec.read_argv_ptr_k] /
  [CatExec.read_argv_byte_k]; everything is derived from
  [StackLayout.build_stack_bytes] by list surgery + [read_at_offset].

  The entry draw ([Run.en_draw]) fixes the AT_RANDOM bytes
  ([at_random_bytes] of `draw.ed_random`); AT_HWCAP is the auxv's fourth
  pair (10 pairs / 20 words, `auxv_size` 160); the mapped image is
  [Run.entry_stack_image] (block ++ page slack).

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  * The  `Section Layout` variables become EXPLICIT parameters, in
    the order ([segs], [ph], [sp], [rdraw], [av], [ev], [uid],
    [hw], then the hypotheses [Hva], [Hve], [Hsp_lo], [Hsp_hi]), exactly
    as [Common.ArgvEnv] does.
  * `Z` → `Int`, `bv_unsigned w` → `(w.toNat : Int)`,
    `Z.of_nat (length l)` → `(l.length : Int)`, `Z_to_bv n z` →
    `BitVec.ofInt n z`, the nat-indexed `nth k l d` → `l[k]?.getD d`,
    `firstn`/`skipn` → `List.take`/`List.drop`, `repeat x n` →
    `List.replicate n x`, `2^64` (over `Z`) → `((2 ^ 64 : Nat) : Int)`.
  * ASSOCIATIVITY.  `List.append_assoc` is also what makes the existential
    splits (`∃ post, bsb = … ++ post`) still infer their witness, exactly
    the way elaboration does — see the `obtain ⟨post, E⟩` steps.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.ArgvEnv

namespace LinuxSem.Common.RefLayout

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
open LinuxSem.Common.ArgvEnv

variable [fx : FPState]

/- =================================================================
   Generic list / rdn helpers
   ================================================================= -/

/-- [rdn] of [k] bytes at offset [off] out of an [n]-byte read: the
    [skipn]-flavoured companion of [SeqExec.rdn_firstn] (and a different
    statement from [SeqExec.rdn_skipn], see the header).
-/
theorem rdn_skipn (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte) (off k : Nat),
      rdn segs mem a n = some bs → off + k ≤ n →
      rdn segs mem (a + nat_to_word off) k = some ((bs.drop off).take k) := by
  induction n with
  | zero =>
    intro a bs off k H Hk
    have hoff : off = 0 := by omega
    have hk : k = 0 := by omega
    subst hoff
    subst hk
    rw [rdn_zero, Option.some.injEq] at H
    subst H
    rw [word_add_0, rdn_zero]
    rfl
  | succ n ih =>
    intro a bs off k H Hk
    cases hb : rdn_byte segs mem a with
    | none =>
      rw [rdn_succ_none segs mem a n hb] at H
      exact absurd H (by simp)
    | some b =>
      rw [rdn_succ_byte segs mem a n b hb] at H
      cases hr : rdn segs mem (a + 1) n with
      | none => rw [hr] at H; simp at H
      | some rest =>
        rw [hr] at H
        simp only [Option.bind_some, Option.some.injEq] at H
        subst H
        have Hfull : rdn segs mem a (n + 1) = some (b :: rest) := by
          rw [rdn_succ_byte segs mem a n b hb, hr]
          rfl
        cases off with
        | zero =>
          rw [word_add_0]
          exact rdn_firstn segs mem (n + 1) a (b :: rest) k Hfull (by omega)
        | succ off' =>
          rw [add_nat_to_word_succ,
            show (b :: rest).drop (off' + 1) = rest.drop off' from rfl]
          exact ih (a + 1) rest off' k hr (by omega)

/-- `firstn` of an append at exactly the first summand's length. -/
theorem firstn_app_exact {A : Type} (l1 l2 : List A) (n : Nat) (H : l1.length = n) :
    (l1 ++ l2).take n = l1 := by
  subst H
  rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]

/-- `skipn` of an append at exactly the first summand's length. -/
theorem skipn_app_exact {A : Type} (l1 l2 : List A) (n : Nat) (H : l1.length = n) :
    (l1 ++ l2).drop n = l2 := by
  subst H
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]

/-- `skipn` of a `repeat` . -/
theorem skipn_repeat' {A : Type} (x : A) (off n : Nat) :
    (List.replicate n x).drop off = List.replicate (n - off) x :=
  List.drop_replicate

/-- `firstn` of a `repeat` . -/
theorem firstn_repeat' {A : Type} (x : A) (k n : Nat) (H : k ≤ n) :
    (List.replicate n x).take k = List.replicate k x := by
  rw [List.take_replicate, Nat.min_eq_left H]

/-- The composition: `firstn k` of a `skipn off` of a `repeat`. -/
theorem repeat_firstn_skipn {A : Type} (x : A) (n off k : Nat) (H : off + k ≤ n) :
    ((List.replicate n x).drop off).take k = List.replicate k x := by
  rw [skipn_repeat', firstn_repeat' _ _ _ (by omega)]

/-- The [mid] piece of a left-grouped `(pre ++ mid) ++ post` chain, read back
    by its own `drop`/`take` pair. -/
theorem drop_take_mid {A : Type} (p m q : List A) (k n : Nat)
    (Hk : p.length = k) (Hn : m.length = n) :
    (((p ++ m) ++ q).drop k).take n = m := by
  subst Hk
  subst Hn
  rw [List.drop_append_of_le_length (l₁ := p ++ m) (i := p.length) (by simp),
    List.drop_append_of_le_length (l₁ := p) (i := p.length) (by simp),
    List.drop_length, List.nil_append, List.take_left]

/- =================================================================
   Layout abbreviations (extending CatExec's cat_* family)
   ================================================================= -/

/-- The k-th envp pointer value. -/
def cat_envp_ptr (sp : word) (av ev : List (List byte)) (k : Nat) : word :=
  ((string_addrs (cat_env_base sp av ev) ev).1[k]?).getD (BitVec.ofInt 64 0)

/-- Offsets (from sp) of the envp slot array and of the auxv.
-/
def envp_off (av : List (List byte)) : Nat := 8 + 8 * (av.length + 1)

def auxv_off (av ev : List (List byte)) : Nat :=
  8 + 8 * (av.length + 1) + 8 * (ev.length + 1)

/-- The 20 auxv words, in order (type, value, type, value, ...);
    (AT_HWCAP, hw) is the 4th pair. -/
def auxv_words (ph : PhdrInfo) (rnd uid hw : word) : List word :=
  (auxv_entries ph rnd uid hw).flatMap (fun e => [e.1, e.2])

/-- [build_auxv] is the byte image of the flattened (type, value) word list. -/
theorem build_auxv_words (entries : List (word × word)) :
    build_auxv entries = ((entries.flatMap (fun e => [e.1, e.2])).flatMap word_le8) := by
  simp only [build_auxv, List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- [auxv_bytes] is the byte image of [auxv_words]. -/
theorem auxv_bytes_words (ph : PhdrInfo) (rnd uid hw : word) :
    auxv_bytes ph rnd uid hw = (auxv_words ph rnd uid hw).flatMap word_le8 := by
  unfold auxv_bytes auxv_words
  exact build_auxv_words _

/-- The auxv is 20 words (10 pairs). -/
theorem length_auxv_words (ph : PhdrInfo) (rnd uid hw : word) :
    (auxv_words ph rnd uid hw).length = 20 := by
  simp [auxv_words, auxv_entries]

/- =================================================================
   The initial-stack layout section

    `Section Layout` variables are explicit parameters in the
    order; [bsb] and [stk] are spelled out at every use site.
   ================================================================= -/

section Layout

variable (segs : List Segment) (ph : PhdrInfo) (sp : word) (rdw : EntryDraw)
  (av ev : List (List byte)) (uid hw : word)

/-- The initial stack image sits below `2^64` . -/
theorem lay_bsb_nw (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    (sp.toNat : Int)
      + ((build_stack_bytes ph sp av ev uid hw rdw).length : Int) < ((2 ^ 64 : Nat) : Int) :=
  bsb_nw ph sp av ev uid hw rdw Hva Hve Hsp_hi

/-- The argv length bounds, as [`Nat`] facts. -/
theorem lay_len_av (Hva : valid_argv av) : 1 ≤ av.length ∧ av.length ≤ 1024 :=
  ⟨valid_argv_nonempty av Hva, Int.ofNat_le.mp (valid_argv_len av Hva)⟩

/-- The envp length bound. -/
theorem lay_len_ev (Hve : valid_envp ev) : ev.length ≤ 256 := by
  unfold valid_envp at Hve
  exact Int.ofNat_le.mp Hve.1

/-- The master decomposition: struct prefix pieces named. -/
theorem bsb_decomp :
    ∃ strs_tail,
      build_stack_bytes ph sp av ev uid hw rdw
        = (word_le8 (len_word av)
            ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8)
          ++ word_le8 (BitVec.ofInt 64 0)
          ++ (string_addrs (cat_env_base sp av ev) ev).1.flatMap word_le8
          ++ word_le8 (BitVec.ofInt 64 0)
          ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
          ++ strs_tail := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    unfold build_stack_bytes cat_env_base cat_string_base cat_struct_size
    simp only []
    rw [length_auxv_bytes, string_addrs_pair av, string_addrs_pair ev]
    simp only [List.append_assoc]
    rfl

/-- The `argc ++ argv pointers` prefix is `8 + 8 * argc` bytes long. -/
theorem len_argc_argv :
    (word_le8 (len_word av)
        ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8).length
      = 8 + 8 * av.length := by
  rw [List.length_append, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst]

/-- The envp pointer run is `8 * envc` bytes long. -/
theorem len_envp_ptrs :
    ((string_addrs (cat_env_base sp av ev) ev).1.flatMap word_le8).length
      = 8 * ev.length := by
  rw [length_flat_map_le8, length_string_addrs_fst]

/-- The alignment pad brings a length up to a multiple of 8:
    `n + (8 - n % 8) % 8` is `0` modulo 8.   reaches the same fact
    inside `bsb_random_split` by a `Z.mod_pos_bound` and a
    `Zplus_mod_idemp_*` chain; this tree states it once, in `Nat`, and lets
    `omega` close it (it handles `%` by the literal 8). -/
theorem add_pad_mod8 (n : Nat) : (n + (8 - n % 8) % 8) % 8 = 0 := by omega

/-- The mapped image the layout reads go through: the block plus the page
    slack above it . -/
abbrev stk (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rdw : EntryDraw) : word → Option byte :=
  stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdw)

/-! The struct-prefix pieces of [bsb_decomp], named once.      -/

/-- `argc ++ the argv pointer run`. -/
def argcPtrs (sp : word) (av ev : List (List byte)) : List byte :=
  word_le8 (len_word av)
    ++ (string_addrs (cat_string_base sp av ev) av).1.flatMap word_le8

/-- The argv NULL word. -/
def argvNull : List byte := word_le8 (BitVec.ofInt 64 0)

/-- The envp pointer run. -/
def envpPtrs (sp : word) (av ev : List (List byte)) : List byte :=
  (string_addrs (cat_env_base sp av ev) ev).1.flatMap word_le8

/-- The envp NULL word. -/
def envpNull : List byte := word_le8 (BitVec.ofInt 64 0)

/-- The first [k] envp pointer slots. -/
def envpPtrsTake (sp : word) (av ev : List (List byte)) (k : Nat) : List byte :=
  ((string_addrs (cat_env_base sp av ev) ev).1.take k).flatMap word_le8

/-- The [k]-th envp pointer slot's word. -/
def envpPtrWord (sp : word) (av ev : List (List byte)) (k : Nat) : List byte :=
  word_le8 (((string_addrs (cat_env_base sp av ev) ev).1[k]?).getD (BitVec.ofInt 64 0))

/-- argv NULL terminator at [sp + 8 + 8*argc]. -/
theorem read_argv_null (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    rdn segs (stk ph sp av ev uid hw rdw) (sp + nat_to_word (8 + 8 * av.length)) 8
      = some (word_le8 (BitVec.ofInt 64 0)) := by
  obtain ⟨tl, E0⟩ := bsb_decomp ph sp rdw av ev uid hw
  obtain ⟨post, E⟩ : ∃ post, build_stack_bytes ph sp av ev uid hw rdw
      = argcPtrs sp av ev ++ argvNull ++ post := ⟨_, by
    simpa only [argcPtrs, argvNull, List.append_assoc] using E0⟩
  have h := read_at_offset_image segs ph sp av ev uid hw rdw
    (argcPtrs sp av ev) argvNull post 8 E (length_n_to_le_8 _)
    (lay_bsb_nw ph sp rdw av ev uid hw Hva Hve Hsp_hi)
  have hidx : 8 + 8 * av.length = (argcPtrs sp av ev).length := by
    simp only [argcPtrs, List.length_append, length_n_to_le_8, length_flat_map_le8,
      length_string_addrs_fst]
  rw [hidx]
  exact h

/-- k-th envp pointer slot. -/
theorem read_envp_ptr_k (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < ev.length) :
    rdn segs (stk ph sp av ev uid hw rdw) (sp + nat_to_word (envp_off av + 8 * k)) 8
      = some (word_le8 (cat_envp_ptr sp av ev k)) := by
  obtain ⟨tl, E0⟩ := bsb_decomp ph sp rdw av ev uid hw
  have Hk' : k < (string_addrs (cat_env_base sp av ev) ev).1.length := by
    rw [length_string_addrs_fst]; exact Hk
  rw [flat_map_le8_decomp _ k Hk'] at E0
  obtain ⟨post, E⟩ : ∃ post, build_stack_bytes ph sp av ev uid hw rdw
      = argcPtrs sp av ev ++ argvNull ++ envpPtrsTake sp av ev k
        ++ envpPtrWord sp av ev k ++ post := ⟨_, by
    simpa only [argcPtrs, argvNull, envpPtrsTake, envpPtrWord, List.append_assoc] using E0⟩
  have h := read_at_offset_image segs ph sp av ev uid hw rdw
    (argcPtrs sp av ev ++ argvNull ++ envpPtrsTake sp av ev k)
    (envpPtrWord sp av ev k) post 8 E (length_n_to_le_8 _)
    (lay_bsb_nw ph sp rdw av ev uid hw Hva Hve Hsp_hi)
  have hidx : envp_off av + 8 * k
      = (argcPtrs sp av ev ++ argvNull ++ envpPtrsTake sp av ev k).length := by
    simp only [List.length_append, argcPtrs, len_argc_argv sp av ev, argvNull,
      length_n_to_le_8, envpPtrsTake, length_flat_map_le8, List.length_take,
      length_string_addrs_fst, Nat.min_eq_left (Nat.le_of_lt Hk)]
    unfold envp_off
    omega
  rw [hidx]
  unfold cat_envp_ptr
  exact h

/-- envp NULL terminator. -/
theorem read_envp_null (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    rdn segs (stk ph sp av ev uid hw rdw) (sp + nat_to_word (envp_off av + 8 * ev.length)) 8
      = some (word_le8 (BitVec.ofInt 64 0)) := by
  obtain ⟨tl, E0⟩ := bsb_decomp ph sp rdw av ev uid hw
  obtain ⟨post, E⟩ : ∃ post, build_stack_bytes ph sp av ev uid hw rdw
      = argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev ++ envpNull ++ post := ⟨_, by
    simpa only [argcPtrs, argvNull, envpPtrs, envpNull, List.append_assoc] using E0⟩
  have h := read_at_offset_image segs ph sp av ev uid hw rdw
    (argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev) envpNull post 8 E
    (length_n_to_le_8 _) (lay_bsb_nw ph sp rdw av ev uid hw Hva Hve Hsp_hi)
  have hidx : envp_off av + 8 * ev.length
      = (argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev).length := by
    simp only [List.length_append, argcPtrs, len_argc_argv sp av ev, argvNull,
      length_n_to_le_8, envpPtrs, len_envp_ptrs sp av ev]
    unfold envp_off
    omega
  rw [hidx]
  exact h

/-- The whole auxv (160 bytes). -/
theorem read_auxv_all (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    rdn segs (stk ph sp av ev uid hw rdw) (sp + nat_to_word (auxv_off av ev)) 160
      = some (auxv_bytes ph (at_random_ptr sp av ev) uid hw) := by
  obtain ⟨tl, E0⟩ := bsb_decomp ph sp rdw av ev uid hw
  obtain ⟨post, E⟩ : ∃ post, build_stack_bytes ph sp av ev uid hw rdw
      = argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev ++ envpNull
        ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw ++ post := ⟨_, by
    simpa only [argcPtrs, argvNull, envpPtrs, envpNull, List.append_assoc] using E0⟩
  have h := read_at_offset_image segs ph sp av ev uid hw rdw
    (argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev ++ envpNull)
    (auxv_bytes ph (at_random_ptr sp av ev) uid hw) post 160 E
    (length_auxv_bytes _ _ _ _) (lay_bsb_nw ph sp rdw av ev uid hw Hva Hve Hsp_hi)
  have hidx : auxv_off av ev
      = (argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev ++ envpNull).length := by
    simp only [List.length_append, argcPtrs, len_argc_argv sp av ev, argvNull,
      length_n_to_le_8, envpPtrs, len_envp_ptrs sp av ev, envpNull]
    unfold auxv_off
    omega
  rw [hidx]
  exact h

/-- One auxv word. -/
theorem read_auxv_word (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (j : Nat) (Hj : j < 20) :
    rdn segs (stk ph sp av ev uid hw rdw) (sp + nat_to_word (auxv_off av ev + 8 * j)) 8
      = some (word_le8 (((auxv_words ph (at_random_ptr sp av ev) uid hw)[j]?).getD
          (BitVec.ofInt 64 0))) := by
  rw [← nat_to_word_add_merge sp (auxv_off av ev) (8 * j)]
  rw [rdn_skipn segs (stk ph sp av ev uid hw rdw) 160 _
    (auxv_bytes ph (at_random_ptr sp av ev) uid hw) (8 * j) 8
    (read_auxv_all segs ph sp rdw av ev uid hw Hva Hve Hsp_hi) (by omega)]
  congr 1
  rw [auxv_bytes_words]
  rw [flat_map_le8_decomp _ j (by rw [length_auxv_words]; exact Hj)]
  have hA : (((auxv_words ph (at_random_ptr sp av ev) uid hw).take j).flatMap word_le8).length
      = 8 * j := by
    rw [length_flat_map_le8, List.length_take, length_auxv_words,
      Nat.min_eq_left (by omega)]
  exact drop_take_mid _ _ _ (8 * j) 8 hA (length_n_to_le_8 _)

/- ---------------------------------------------------------------
   AT_RANDOM block
   --------------------------------------------------------------- -/

/-- The draw-INDEPENDENT part of the image: the struct, the strings and the
    alignment pad.  name for the witness  introduces
    inline in `bsb_random_split` (`exists pre, ...`), so that the three
    facts about it can be stated once each. -/
def bsbRaw (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word) :
    List byte :=
  argcPtrs sp av ev ++ argvNull ++ envpPtrs sp av ev ++ envpNull
    ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
    ++ flatten_strings av ++ flatten_strings ev

/-- `bsbRaw` followed by the alignment pad. -/
def bsbPre (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word) :
    List byte :=
  bsbRaw ph sp av ev uid hw
    ++ List.replicate ((8 - (bsbRaw ph sp av ev uid hw).length % 8) % 8)
        (BitVec.ofInt 8 0)

/-- The raw prefix's length: the struct pieces, the auxv and the strings. -/
theorem bsbRaw_length (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word) :
    (bsbRaw ph sp av ev uid hw).length
      = ((8 + (av.length + 1) * 8 + (ev.length + 1) * 8 + auxv_size)
          + (flatten_strings av).length) + (flatten_strings ev).length := by
  simp only [bsbRaw, List.length_append, argcPtrs, len_argc_argv sp av ev, argvNull,
    length_n_to_le_8, envpPtrs, len_envp_ptrs sp av ev, envpNull, length_auxv_bytes,
    length_flatten_strings]
  omega

/-- The prefix's length is the raw length plus the pad. -/
theorem bsbPre_length (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word) :
    (bsbPre ph sp av ev uid hw).length
      = (bsbRaw ph sp av ev uid hw).length
        + ((8 - (bsbRaw ph sp av ev uid hw).length % 8) % 8) := by
  simp only [bsbPre, List.length_append, List.length_replicate]

/-- The pad brings the prefix's length up to a multiple of 8. -/
theorem bsbPre_mod8 (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word) :
    ((bsbPre ph sp av ev uid hw).length : Nat) % 8 = 0 := by
  rw [bsbPre_length]
  exact add_pad_mod8 _

/-- The image is the prefix plus the draw.

     closes this by `rewrite (string_addrs_pair …)` plus
    `app_assoc`; in Lean the two sides are the same term once the auxv's
    length is rewritten to `auxv_size` and the string-address pairs are
    split, which is what the final `rw` leaves to the kernel. -/
theorem bsbPre_image (ph : PhdrInfo) (sp : word) (av ev : List (List byte)) (uid hw : word)
    (rdw : EntryDraw) :
    build_stack_bytes ph sp av ev uid hw rdw
      = bsbPre ph sp av ev uid hw ++ at_random_bytes rdw.ed_random := by
  unfold build_stack_bytes bsbPre bsbRaw argcPtrs argvNull envpPtrs envpNull
    cat_env_base cat_string_base cat_struct_size
  simp only []
  rw [length_auxv_bytes, string_addrs_pair av, string_addrs_pair ev]

/-- The AT_RANDOM pointer is the prefix's end. -/
theorem at_random_ptr_eq_bsbPre (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) :
    at_random_ptr sp av ev = sp + nat_to_word (bsbPre ph sp av ev uid hw).length := by
  rw [bsbPre_length, bsbRaw_length]
  unfold at_random_ptr
  simp only [auxv_size]

/-- [bsb] = raw ++ pad ++ at_random_bytes with |raw ++ pad| = the offset
    [at_random_ptr] adds to [sp]. -/
theorem bsb_random_split (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rdw : EntryDraw) :
    ∃ pre : List byte,
      build_stack_bytes ph sp av ev uid hw rdw = pre ++ at_random_bytes rdw.ed_random
        ∧ at_random_ptr sp av ev = sp + nat_to_word pre.length
        ∧ ((pre.length : Nat) : Int) % 8 = 0 := by
  refine ⟨bsbPre ph sp av ev uid hw, bsbPre_image ph sp av ev uid hw rdw,
    at_random_ptr_eq_bsbPre ph sp av ev uid hw, ?_⟩
  have h := bsbPre_mod8 ph sp av ev uid hw
  show ((bsbPre ph sp av ev uid hw).length : Int) % ((8 : Nat) : Int) = 0
  rw [← Int.natCast_emod, h]
  rfl

/-- The AT_RANDOM block is read back as the draw: [off] is the prefix's
    length, and every 16-byte-window read of the block is a `drop`/`take`
    of [at_random_bytes]. -/
theorem at_random_off (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    ∃ off : Nat,
      at_random_ptr sp av ev = sp + nat_to_word off
        ∧ off + 16 = (build_stack_bytes ph sp av ev uid hw rdw).length
        ∧ ((off : Int) % 8 = 0)
        ∧ ∀ (j n : Nat), j + n ≤ 16 →
            rdn segs (stk ph sp av ev uid hw rdw) (at_random_ptr sp av ev + nat_to_word j) n
              = some (((at_random_bytes rdw.ed_random).drop j).take n) := by
  obtain ⟨pre, E, Hp, Hmod⟩ := bsb_random_split ph sp av ev uid hw rdw
  have HL : (at_random_bytes rdw.ed_random).length = 16 := length_at_random_bytes _
  refine ⟨pre.length, Hp, ?_, Hmod, ?_⟩
  · rw [E, List.length_append, HL]
  · intro j n Hjn
    rw [Hp, nat_to_word_add_merge]
    -- split the draw at [j] and then at [n]: `pre ++ take j ++ take n ++ rest`
    have hr : at_random_bytes rdw.ed_random
        = (at_random_bytes rdw.ed_random).take j
          ++ (((at_random_bytes rdw.ed_random).drop j).take n
            ++ ((at_random_bytes rdw.ed_random).drop j).drop n) := by
      simp only [List.take_append_drop]
    obtain ⟨post, E'⟩ : ∃ post, build_stack_bytes ph sp av ev uid hw rdw
        = pre ++ (at_random_bytes rdw.ed_random).take j
          ++ ((at_random_bytes rdw.ed_random).drop j).take n ++ post :=
      ⟨_, by
        conv => lhs; rw [E, hr]
        simp only [List.append_assoc]
        rfl⟩
    have h := read_at_offset_image segs ph sp av ev uid hw rdw
      (pre ++ (at_random_bytes rdw.ed_random).take j)
      (((at_random_bytes rdw.ed_random).drop j).take n) post n E'
      (by rw [List.length_take, List.length_drop, HL]; omega)
      (lay_bsb_nw ph sp rdw av ev uid hw Hva Hve Hsp_hi)
    have hlen : (pre ++ (at_random_bytes rdw.ed_random).take j).length = pre.length + j := by
      rw [List.length_append, List.length_take, HL, Nat.min_eq_left (by omega)]
    rw [hlen] at h
    exact h

/- ---------------------------------------------------------------
   Bounds
   --------------------------------------------------------------- -/

/-- The image's length bound. -/
theorem lay_bsb_len (Hva : valid_argv av) (Hve : valid_envp ev) :
    ((build_stack_bytes ph sp av ev uid hw rdw).length : Int) ≤ 2240000 :=
  bsb_bound ph sp av ev uid hw rdw Hva Hve

/-- The auxv, and the AT_RANDOM block above it, fit inside the image. -/
theorem auxv_off_bound :
    auxv_off av ev + 160 + 16 ≤ (build_stack_bytes ph sp av ev uid hw rdw).length := by
  have hA : (auxv_bytes ph (at_random_ptr sp av ev) uid hw).length = 160 := by
    rw [length_auxv_bytes]; rfl
  unfold build_stack_bytes auxv_off
  simp only []
  rw [string_addrs_pair av, string_addrs_pair ev]
  simp only [List.length_append, length_at_random_bytes, List.length_replicate,
    length_flat_map_le8, length_string_addrs_fst, length_n_to_le_8, length_flatten_strings, hA]
  omega

/- ---------------------------------------------------------------
   envp / argv pointer values
   --------------------------------------------------------------- -/

/-- The k-th envp pointer as an offset from [sp]. -/
theorem cat_envp_ptr_eq (k : Nat) (Hk : k < ev.length) :
    cat_envp_ptr sp av ev k
      = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
          + total_arg_bytes_nat (ev.take k)) := by
  unfold cat_envp_ptr
  rw [nth_string_addrs ev (cat_env_base sp av ev) k Hk]
  unfold cat_env_base cat_string_base
  rw [nat_to_word_add_merge, nat_to_word_add_merge, Nat.add_assoc]

/-- The first [k] envp strings stay under the envp byte bound. -/
theorem total_firstn_ev_bound (Hve : valid_envp ev) (k : Nat) :
    ((total_arg_bytes_nat (ev.take k) : Nat) : Int) ≤ 131072 := by
  have h1 : total_arg_bytes ev ≤ 131072 := Hve.2.1
  rw [total_arg_bytes_Z] at h1
  have h2 := total_arg_bytes_firstn_le k ev
  omega

/-- The argv struct (up to the end of the argv strings) stays under
    `2097152 + 10424`. -/
theorem struct_av_bound (Hva : valid_argv av) (Hve : valid_envp ev) :
    ((cat_struct_size av ev + total_arg_bytes_nat av : Nat) : Int) ≤ 2107576 := by
  have hl : (av.length : Int) ≤ 1024 := valid_argv_len av Hva
  have hle : (ev.length : Int) ≤ 256 := Hve.1
  have hta : total_arg_bytes av ≤ 2097152 := Hva.2.1
  rw [total_arg_bytes_Z] at hta
  unfold cat_struct_size auxv_size
  push_cast
  omega

/-- The k-th envp pointer's unsigned value, as a `Z` offset from [sp]
    (in range, so [u_Z2bv] applies). -/
theorem u_cat_envp_ptr (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int)) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < ev.length) :
    ((cat_envp_ptr sp av ev k).toNat : Int)
      = (sp.toNat : Int) + ((cat_struct_size av ev + total_arg_bytes_nat av
          + total_arg_bytes_nat (ev.take k) : Nat) : Int) := by
  rw [cat_envp_ptr_eq sp av ev k Hk, word_add_nat]
  have h1 := struct_av_bound av ev Hva Hve
  have h2 := total_firstn_ev_bound ev Hve k
  have hsp : (sp.toNat : Int) ≤ 0x800000000000 := Hsp_hi
  have hsplo : (0 : Int) ≤ (sp.toNat : Int) := by
    have := Hsp_lo; unfold sp_window_lo at this; omega
  rw [u_Z2bv _ (by push_cast; omega) (by push_cast; omega)]

/-- An envp pointer is never NULL. -/
theorem cat_envp_ptr_nz (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int)) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < ev.length) :
    ((cat_envp_ptr sp av ev k).toNat : Int) ≠ 0 := by
  rw [u_cat_envp_ptr sp av ev Hva Hve Hsp_lo Hsp_hi k Hk]
  have hsp : (0x7fff80000000 : Int) ≤ (sp.toNat : Int) := Hsp_lo
  have hk : (0 : Int) ≤ ((total_arg_bytes_nat (ev.take k) : Nat) : Int) := by
    push_cast; omega
  have h1 := struct_av_bound av ev Hva Hve
  omega

/-- The k-th argv pointer's unsigned value, as a `Z` offset from [sp]. -/
theorem u_cat_argv_ptr (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int)) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < av.length) :
    ((cat_argv_ptr sp av ev k).toNat : Int)
      = (sp.toNat : Int) + ((cat_struct_size av ev
          + total_arg_bytes_nat (av.take k) : Nat) : Int) := by
  rw [cat_argv_ptr_offset sp av ev k Hk]
  unfold cat_string_base
  rw [nat_to_word_add_merge, word_add_nat]
  have h1 := struct_av_bound av ev Hva Hve
  have h2 := total_arg_bytes_firstn_le k av
  have hsp : (sp.toNat : Int) ≤ 0x800000000000 := Hsp_hi
  have hsplo : (0 : Int) ≤ (sp.toNat : Int) := by
    have := Hsp_lo; unfold sp_window_lo at this; omega
  rw [u_Z2bv _ (by push_cast; omega) (by push_cast; omega)]

/-- An argv string's length bound. -/
theorem argv_str_len (Hva : valid_argv av) (k : Nat) (Hk : k < av.length) :
    (((av[k]?.getD []).length : Nat) : Int) ≤ 131071 :=
  valid_argv_str_len av k Hva Hk

/-- The auxv word list, spelled out. -/
theorem auxv_words_eq (rnd : word) :
    auxv_words ph rnd uid hw =
      [AT_PHDR, BitVec.ofInt 64 (ph.ph_addr : Int), AT_PHENT,
        BitVec.ofInt 64 (ph.ph_ent : Int), AT_PHNUM,
        BitVec.ofInt 64 (ph.ph_num : Int), AT_HWCAP, hw, AT_PAGESZ,
        BitVec.ofInt 64 4096, AT_UID, uid, AT_EUID, uid, AT_SECURE,
        BitVec.ofInt 64 0, AT_RANDOM, rnd, AT_NULL, BitVec.ofInt 64 0] := rfl

/-- AT_RANDOM pointer facts used by `__init_ssp`/`memcpy`; the bytes
    themselves are the draw.
-/
theorem rnd_facts (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int)) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (Hal : (sp.toNat : Int) % 16 = 0) :
    ((sp.toNat : Int) ≤ ((at_random_ptr sp av ev).toNat : Int))
    ∧ ((at_random_ptr sp av ev).toNat : Int) + 16
        ≤ (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rdw).length : Int)
    ∧ (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rdw).length : Int)
        < ((2 ^ 64 : Nat) : Int)
    ∧ ((at_random_ptr sp av ev).toNat : Int) % 8 = 0
    ∧ ∀ (j n : Nat), j + n ≤ 16 →
        rdn segs (stk ph sp av ev uid hw rdw)
            (BitVec.ofInt 64 (((at_random_ptr sp av ev).toNat : Int) + (j : Int))) n
          = some (((at_random_bytes rdw.ed_random).drop j).take n) := by
  obtain ⟨off, Hp, Hlen, Hmod, Hrd⟩ := at_random_off segs ph sp rdw av ev uid hw Hva Hve Hsp_hi
  have Hnw := lay_bsb_nw ph sp rdw av ev uid hw Hva Hve Hsp_hi
  have Hbl := lay_bsb_len ph sp rdw av ev uid hw Hva Hve
  have hspTop : (sp.toNat : Int) ≤ 0x800000000000 := Hsp_hi
  have hspBot : (0 : Int) ≤ (sp.toNat : Int) := by
    have := Hsp_lo; unfold sp_window_lo at this; omega
  have Hu : ((at_random_ptr sp av ev).toNat : Int) = (sp.toNat : Int) + (off : Int) := by
    rw [Hp, word_add_nat]
    exact u_Z2bv _ (by omega) (by omega)
  have hsp8 : (sp.toNat : Int) % 8 = 0 := by
    have h16 : (sp.toNat : Int) % 16 % 8 = (sp.toNat : Int) % 8 :=
      Int.emod_emod_of_dvd _ (m := 8) (k := 16) (by decide)
    rw [← h16, Hal]
    rfl
  rw [Hu]
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [Int.add_emod, hsp8, Hmod]
    rfl
  · intro j n Hjn
    rw [← Hu, ← word_add_nat]
    exact Hrd j n Hjn

end Layout

/-! -/

/-- The envp slot array starts `8 + 8*(argc+1)` bytes above [sp]. -/
example : envp_off [] = 16 := by decide

example : envp_off [[1, 2]] = 24 := by decide

/-- …and the auxv sits above the envp pointers. -/
example : auxv_off [] [] = 24 := by decide

example : auxv_off [[1, 2]] [[3]] = 40 := by decide

/-- The auxv word list is the ten (type, value) pairs flattened. -/
example : (auxv_words ⟨0x1000, 56, 2⟩ 0 0 hwcap_rv64gc).length = 20 := by decide

example : (auxv_words ⟨0x1000, 56, 2⟩ 0 0 hwcap_rv64gc)[0]? = some AT_PHDR := by decide

example : (auxv_words ⟨0x1000, 56, 2⟩ 0 0 hwcap_rv64gc)[1]? = some 0x1000 := by decide

/-- AT_HWCAP is the 4th pair, i.e. words 6 and 7. -/
example : (auxv_words ⟨0x1000, 56, 2⟩ 0 0 hwcap_rv64gc)[6]? = some AT_HWCAP := by decide

example : (auxv_words ⟨0x1000, 56, 2⟩ 0 0 hwcap_rv64gc)[7]? = some hwcap_rv64gc := by decide

/-- `bsb_random_split` at a concrete layout: the image is the prefix plus the
    16 bytes of the draw… -/
example : build_stack_bytes ⟨0x1000, 56, 2⟩ 0x7fff0000 [] [[1, 2]] 0 hwcap_rv64gc
      ⟨0xDEADBEEF, fun _ => 0⟩
    = bsbPre ⟨0x1000, 56, 2⟩ 0x7fff0000 [] [[1, 2]] 0 hwcap_rv64gc
      ++ at_random_bytes 0xDEADBEEF := by decide

/-- …whose length is a multiple of 8… -/
example : (bsbPre ⟨0x1000, 56, 2⟩ 0x7fff0000 [] [[1, 2]] 0 hwcap_rv64gc).length % 8 = 0 := by
  decide

/-- …and [at_random_ptr] is exactly where that prefix ends. -/
example : at_random_ptr 0x7fff0000 [] [[1, 2]]
    = 0x7fff0000 + nat_to_word (bsbPre ⟨0x1000, 56, 2⟩ 0x7fff0000 [] [[1, 2]] 0
        hwcap_rv64gc).length := by decide

/-- The k-th envp pointer is the string's own address: the struct (200 bytes
    for one argv and one envp string) plus the argv bytes (3). -/
example : cat_envp_ptr 0x1000 [[1, 2]] [[3]] 0 = 0x1000 + 203 := by decide

/-- The second envp string sits one NUL-terminated byte above the first (the
    struct grows by one envp slot, 8 bytes, and the first string is 2 bytes). -/
example : cat_envp_ptr 0x1000 [[1, 2]] [[3], [4]] 1 = 0x1000 + 213 := by decide


/-- `envp_off` / `auxv_off` against the image itself: for `argv = []` and
    `envp = [[1,2]]` the argv NULL sits at offset 8, the envp pointer run at
    `envp_off [] = 16`, the envp NULL at `envp_off [] + 8*1 = 24`, and the
    auxv's first word (`AT_PHDR`) at `auxv_off [] [[1,2]] = 40`. -/
example : ((build_stack_bytes ⟨0x1000, 56, 2⟩ 0x1000 [] [[1, 2]] 0 hwcap_rv64gc
    ⟨0, fun _ => 0⟩).drop (8 + 8 * ([] : List (List byte)).length)).take 8
    = word_le8 (BitVec.ofInt 64 0) := by decide

example : ((build_stack_bytes ⟨0x1000, 56, 2⟩ 0x1000 [] [[1, 2]] 0 hwcap_rv64gc
    ⟨0, fun _ => 0⟩).drop (envp_off [] + 8 * 1)).take 8
    = word_le8 (BitVec.ofInt 64 0) := by decide

example : ((build_stack_bytes ⟨0x1000, 56, 2⟩ 0x1000 [] [[1, 2]] 0 hwcap_rv64gc
    ⟨0, fun _ => 0⟩).drop (auxv_off [] [[1, 2]])).take 8 = word_le8 AT_PHDR := by decide

end LinuxSem.Common.RefLayout
