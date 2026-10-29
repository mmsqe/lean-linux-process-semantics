/-
  * LinuxProcessSem.Checks.Sys.Prelude — the checkers' shared helpers, reflections and tactics

  Shared infrastructure for the checkers below it: this one mirrors no
  kernel source, and holds nothing syscall-specific.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  Every definition and lemma keeps the name the statements below use.  A
  few spellings follow Lean's library: `firstn`/`skipn` are
  `List.take`/`List.drop`, `existsb`/`forallb` are `List.any`/`List.all`,
  `Nat.eqb` is `==`, and integer-valued lengths and unsigned values are the
  `Int` casts of `.toNat`.  `bv_eqb_eq` lives in `Fs`, so it is cited as
  `Fs.bv_eqb_eq`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs

namespace LinuxSem.Checks.Sys.Prelude

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall (record_copyins record_copyins_ok_empty)
open LinuxSem.LinuxProcessSem.Sys.Uaccess (write_source)

/-- The spec monad's [bind] under an unambiguous name.  Lean's root [bind]
    is [Bind.bind], so the unqualified name is ambiguous; the notation
    gives every statement below one spelling.  (Tactic arguments still need
    the fully qualified name: `unfold` takes an identifier, not a term.) -/
local notation "bind" => LinuxSem.LinuxProcessSem.bind

/-- What an executable check returns: the state and events it accepted, a
    rejection, or a statement that the model does not cover the call. -/
inductive check_result where
  | CheckOk (m : Model) (evs : List event)
  | CheckReject
  | CheckUnmodeled

/- =========================================================================
   Boolean helpers and their reflections
   ========================================================================= -/

theorem bv_eqb_refl {n : Nat} (a : BitVec n) : bv_eqb a a = true :=
  (Fs.bv_eqb_eq a a).mpr rfl

/-- Byte-list equality; bytes are [bv 8]. -/
def listN_eqb : List byte → List byte → Bool
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && listN_eqb r1 r2
  | _, _ => false

theorem listN_eqb_eq (l1 l2 : List byte) : listN_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [listN_eqb]
  | cons a r1 ih =>
    cases l2 with
    | nil => simp [listN_eqb]
    | cons b r2 =>
      simp [listN_eqb, Bool.and_eq_true, Fs.bv_eqb_eq, ih]

/-- Equality of zero-range / unmap-range lists ([eff_zeros],
    [eff_unmaps]). -/
def listNN_eqb : List (word × word) → List (word × word) → Bool
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false

theorem listNN_eqb_eq (l1 l2 : List (word × word)) : listNN_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [listNN_eqb]
  | cons hd r1 ih =>
    obtain ⟨a1, n1⟩ := hd
    cases l2 with
    | nil => simp [listNN_eqb]
    | cons hd2 r2 =>
      obtain ⟨a2, n2⟩ := hd2
      simp [listNN_eqb, Bool.and_eq_true, Fs.bv_eqb_eq, ih]

/-- Equality for the symbolic pre-effect copy ledger. -/
def copy_eqb (c1 c2 : MemCopy) : Bool :=
  bv_eqb c1.copy_src c2.copy_src
  && bv_eqb c1.copy_dst c2.copy_dst
  && bv_eqb c1.copy_len c2.copy_len

def listCopy_eqb : List MemCopy → List MemCopy → Bool
  | [], [] => true
  | c1 :: r1, c2 :: r2 => copy_eqb c1 c2 && listCopy_eqb r1 r2
  | _, _ => false

theorem copy_eqb_eq (c1 c2 : MemCopy) : copy_eqb c1 c2 = true ↔ c1 = c2 := by
  obtain ⟨s1, d1, n1⟩ := c1
  obtain ⟨s2, d2, n2⟩ := c2
  simp [copy_eqb, Bool.and_eq_true, Fs.bv_eqb_eq, and_assoc]

theorem listCopy_eqb_eq (l1 l2 : List MemCopy) : listCopy_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [listCopy_eqb]
  | cons c1 r1 ih =>
    cases l2 with
    | nil => simp [listCopy_eqb]
    | cons c2 r2 =>
      simp [listCopy_eqb, Bool.and_eq_true, copy_eqb_eq, ih]

/-- Equality for syscall write lists: addresses plus their byte strings. -/
def writes_eqb : List (word × List byte) → List (word × List byte) → Bool
  | [], [] => true
  | (a1, bs1) :: r1, (a2, bs2) :: r2 =>
      bv_eqb a1 a2 && listN_eqb bs1 bs2 && writes_eqb r1 r2
  | _, _ => false

theorem writes_eqb_eq (l1 l2 : List (word × List byte)) : writes_eqb l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [writes_eqb]
  | cons hd r1 ih =>
    obtain ⟨a1, bs1⟩ := hd
    cases l2 with
    | nil => simp [writes_eqb]
    | cons hd2 r2 =>
      obtain ⟨a2, bs2⟩ := hd2
      simp [writes_eqb, Bool.and_eq_true, Fs.bv_eqb_eq, listN_eqb_eq, ih]

/-- Range of a 64-bit word's unsigned value, with the modulus exposed as
    the [two_pow_64] constant. -/
theorem word_unsigned_range (w : word) :
    0 ≤ (w.toNat : Int) ∧ (w.toNat : Int) < two_pow_64 := by
  have h := w.isLt
  unfold two_pow_64
  omega

/-- The unsigned value of an in-range errno return. -/
theorem errno_ret_unsigned (e : Int) (h1 : 1 ≤ e) (h2 : e ≤ 4095) :
    ((errno_ret e).toNat : Int) = two_pow_64 - e := by
  unfold errno_ret two_pow_64
  rw [BitVec.toNat_ofInt]
  omega

/-- An error-encoded return value is exactly [errno_ret e] for an errno
    in [1,4095]. -/
theorem errno_ret_error_b (e : Int) (h1 : 1 ≤ e) (h2 : e ≤ 4095) :
    addr_is_error_b (errno_ret e) = true := by
  unfold addr_is_error_b
  rw [errno_ret_unsigned e h1 h2]
  rw [decide_eq_true_eq]
  unfold two_pow_64
  omega

theorem addr_is_error_b_errno (r : word) (H : addr_is_error_b r = true) :
    ∃ e, 1 ≤ e ∧ e ≤ 4095 ∧ r = errno_ret e := by
  have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
  have hr := word_unsigned_range r
  unfold addr_is_error_b at H
  rw [decide_eq_true_eq] at H
  have h1 : 1 ≤ two_pow_64 - (r.toNat : Int) := by omega
  have h2 : two_pow_64 - (r.toNat : Int) ≤ 4095 := by omega
  refine ⟨two_pow_64 - (r.toNat : Int), h1, h2, ?_⟩
  apply BitVec.eq_of_toNat_eq
  apply Int.ofNat_inj.mp
  rw [errno_ret_unsigned (two_pow_64 - (r.toNat : Int)) h1 h2]
  omega

/-- Does [r] encode [-e] for some errno in the injectable set [es]? -/
def errno_ret_in (es : List Int) (r : word) : Bool :=
  es.any (fun e => bv_eqb r (errno_ret e))

theorem errno_ret_in_true (es : List Int) (r : word) :
    errno_ret_in es r = true ↔ ∃ e, e ∈ es ∧ r = errno_ret e := by
  unfold errno_ret_in
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, hmem, heq⟩
    exact ⟨e, hmem, (Fs.bv_eqb_eq r (errno_ret e)).mp heq⟩
  · rintro ⟨e, hmem, rfl⟩
    exact ⟨e, hmem, bv_eqb_refl (errno_ret e)⟩

theorem errno_ret_in_intro (es : List Int) (e : Int) (h : e ∈ es) :
    errno_ret_in es (errno_ret e) = true :=
  (errno_ret_in_true es (errno_ret e)).mpr ⟨e, h, rfl⟩

/-- Every injectable set holds genuine errnos (in [1, 4095]). -/
def errnos_ok (es : List Int) : Bool :=
  es.all (fun e => decide (1 ≤ e) && decide (e ≤ 4095))

theorem errnos_ok_range (es : List Int) (e : Int)
    (Hok : errnos_ok es = true) (HIn : e ∈ es) : 1 ≤ e ∧ e ≤ 4095 := by
  induction es with
  | nil => simp at HIn
  | cons x es ih =>
    simp only [errnos_ok, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at Hok
    obtain ⟨⟨hx1, hx2⟩, hok⟩ := Hok
    rcases List.mem_cons.mp HIn with rfl | hIn
    · exact ⟨hx1, hx2⟩
    · exact ih hok hIn

/-- A value far below the error-encoding window (in particular any
    fd < 2^31, or any grant address below [alloc_top]) never
    matches an injectable errno. -/
theorem errno_ret_in_below (es : List Int) (r : word) (Hok : errnos_ok es = true)
    (Hr : (r.toNat : Int) ≤ two_pow_64 - 4096) : errno_ret_in es r = false := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [errnos_ok, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at Hok
    obtain ⟨⟨he1, he2⟩, hok⟩ := Hok
    show (bv_eqb r (errno_ret e) || errno_ret_in es r) = false
    rw [ih hok]
    simp only [Bool.or_false]
    have hne : r ≠ errno_ret e := by
      intro h
      have h1 := errno_ret_unsigned e he1 he2
      rw [h] at Hr
      rw [h1] at Hr
      omega
    simpa only [bv_eqb] using beq_eq_false_iff_ne.mpr hne

theorem errno_ret_in_fd (es : List Int) (fd : word) (Hok : errnos_ok es = true)
    (Hfd : (fd.toNat : Int) < 2 ^ 31) : errno_ret_in es fd = false := by
  apply errno_ret_in_below es fd Hok
  unfold two_pow_64
  omega

/-- Is [buf, buf+n) writable-mapped?  Decides the delivered-prefix
    writability side condition of [read_spec]. -/
def wmem_ok (i : SyscallInput) (buf n : word) : Bool :=
  match read_bytes_map i.in_wmem buf n with
  | some _ => true
  | none => false

theorem wmem_ok_true (i : SyscallInput) (buf n : word) :
    wmem_ok i buf n = true ↔ read_bytes_map i.in_wmem buf n ≠ none := by
  unfold wmem_ok
  cases read_bytes_map i.in_wmem buf n <;> simp

/-- A prefix of a readable range is readable (and reads the prefix). -/
theorem read_bytes_aux_prefix (k n : Nat) (mp : word → Option byte) (a : word) (w : List byte)
    (Hk : k ≤ n) (Hw : read_bytes_aux mp a n = some w) :
    read_bytes_aux mp a k = some (w.take k) := by
  induction k generalizing n a w with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have Hk' : k ≤ n := by omega
      cases hmp : mp a with
      | none =>
        simp only [read_bytes_aux, hmp] at Hw
        exact nomatch Hw
      | some b =>
        simp only [read_bytes_aux, hmp] at Hw
        cases hr : read_bytes_aux mp (a + 1) n with
        | none =>
          rw [hr] at Hw
          exact nomatch Hw
        | some r =>
          rw [hr] at Hw
          simp only [Option.some.injEq] at Hw
          subst Hw
          simp only [read_bytes_aux, hmp]
          rw [ih (n := n) (a := a + 1) (w := r) Hk' hr]
          simp

theorem read_bytes_map_prefix (mp : word → Option byte) (a len k : word) (w : List byte)
    (Hk : (k.toNat : Int) ≤ (len.toNat : Int))
    (Hw : read_bytes_map mp a len = some w) :
    read_bytes_map mp a k = some (w.take (word_to_nat k)) := by
  rw [read_bytes_map_eq] at Hw ⊢
  exact read_bytes_aux_prefix (word_to_nat k) (word_to_nat len) mp a w
    (by unfold word_to_nat; omega) Hw

/-- Full-range writability implies prefix writability — lets callers
    that established the whole [count] writable keep working. -/
theorem wmem_ok_of_full (i : SyscallInput) (buf count : word) (w : List byte) (k : word)
    (Hw : read_bytes_map i.in_wmem buf count = some w)
    (Hk : (k.toNat : Int) ≤ (count.toNat : Int)) : wmem_ok i buf k = true := by
  unfold wmem_ok
  rw [read_bytes_map_prefix i.in_wmem buf count k w Hk Hw]

/-- Full-readability facts: when the whole range reads, the readable
    prefix IS the whole buffer, of the full length. -/
theorem read_bytes_aux_length (mp : word → Option byte) (k : Nat) (a : word) (w : List byte)
    (Hw : read_bytes_aux mp a k = some w) : w.length = k := by
  induction k generalizing a w with
  | zero =>
    simp [read_bytes_aux] at Hw
    subst Hw
    rfl
  | succ k ih =>
    cases hmp : mp a with
    | none =>
      simp only [read_bytes_aux, hmp] at Hw
      exact nomatch Hw
    | some b =>
      simp only [read_bytes_aux, hmp] at Hw
      cases hr : read_bytes_aux mp (a + 1) k with
      | none =>
        rw [hr] at Hw
        exact nomatch Hw
      | some r =>
        rw [hr] at Hw
        simp only [Option.some.injEq] at Hw
        subst Hw
        simp [ih (a := a + 1) (w := r) hr]

theorem read_bytes_map_length (mp : word → Option byte) (a len : word) (w : List byte)
    (Hw : read_bytes_map mp a len = some w) : (w.length : Int) = (len.toNat : Int) := by
  rw [read_bytes_map_eq] at Hw
  rw [read_bytes_aux_length mp (word_to_nat len) a w Hw]
  rfl

theorem readable_bytes_aux_full (mp : word → Option byte) (k : Nat) (a : word) (w : List byte)
    (Hw : read_bytes_aux mp a k = some w) : readable_bytes_aux mp a k = w := by
  induction k generalizing a w with
  | zero =>
    simp [read_bytes_aux] at Hw
    subst Hw
    rfl
  | succ k ih =>
    cases hmp : mp a with
    | none =>
      simp only [read_bytes_aux, hmp] at Hw
      exact nomatch Hw
    | some b =>
      simp only [read_bytes_aux, hmp] at Hw
      cases hr : read_bytes_aux mp (a + 1) k with
      | none =>
        rw [hr] at Hw
        exact nomatch Hw
      | some r =>
        rw [hr] at Hw
        simp only [Option.some.injEq] at Hw
        subst Hw
        simp only [readable_bytes_aux, hmp, ih (a := a + 1) (w := r) hr]

theorem readable_bytes_full (mp : word → Option byte) (a len : word) (w : List byte)
    (Hw : read_bytes_map mp a len = some w) : readable_bytes mp a len = w := by
  rw [read_bytes_map_eq] at Hw
  rw [readable_bytes_eq]
  exact readable_bytes_aux_full mp (word_to_nat len) a w Hw

/-- A SHORTER walk over a range that reads whole is that range's prefix.
    This is what a write's source is when the kernel's [MAX_RW_COUNT]
    clamp bites: [Uaccess.write_source] walks the clamped count, so a
    proof holding the whole named range still knows exactly which bytes
    the transfer sees, without a bound on the count. -/
theorem readable_bytes_aux_prefix (mp : word → Option byte) (n k : Nat) (a : word) (w : List byte)
    (Hw : read_bytes_aux mp a n = some w) (Hk : k ≤ n) :
    readable_bytes_aux mp a k = w.take k := by
  induction n generalizing k a w with
  | zero =>
    have hk : k = 0 := by omega
    subst hk
    simp [read_bytes_aux] at Hw
    subst Hw
    rfl
  | succ n ih =>
    cases hmp : mp a with
    | none =>
      simp only [read_bytes_aux, hmp] at Hw
      exact nomatch Hw
    | some b =>
      simp only [read_bytes_aux, hmp] at Hw
      cases hr : read_bytes_aux mp (a + 1) n with
      | none =>
        rw [hr] at Hw
        exact nomatch Hw
      | some r =>
        rw [hr] at Hw
        simp only [Option.some.injEq] at Hw
        subst Hw
        cases k with
        | zero => rfl
        | succ k =>
          simp only [readable_bytes_aux, hmp]
          rw [ih (k := k) (a := a + 1) (w := r) hr (by omega)]
          simp

theorem write_source_prefix (mp : word → Option byte) (a len : word) (w : List byte)
    (H : read_bytes_map mp a len = some w) :
    write_source mp a len = w.take (rw_count_clamp len).toNat := by
  rw [read_bytes_map_eq] at H
  unfold write_source
  rw [readable_bytes_eq]
  have hw : word_to_nat (BitVec.ofInt 64 (rw_count_clamp len)) = (rw_count_clamp len).toNat := by
    unfold word_to_nat
    exact Int.ofNat_inj.mp (by
      rw [rw_count_clamp_word len, Int.toNat_of_nonneg (rw_count_clamp_range len).1])
  rw [hw]
  refine readable_bytes_aux_prefix mp (word_to_nat len) (rw_count_clamp len).toNat a w H ?_
  have hle : rw_count_clamp len ≤ (len.toNat : Int) := by
    unfold rw_count_clamp
    exact Int.min_le_left _ _
  have h0 := (rw_count_clamp_range len).1
  have hcast : ((rw_count_clamp len).toNat : Int) ≤ (len.toNat : Int) := by
    rw [Int.toNat_of_nonneg h0]
    exact hle
  exact Int.ofNat_le.mp (by simpa [word_to_nat] using hcast)

/-- A zero-length destination always reads: [read_spec]'s file branch can
    only reach its unwritable case with a NONEMPTY delivered prefix. -/
theorem read_bytes_map_nil (mp : word → Option byte) (a : word) :
    read_bytes_map mp a (len_word ([] : List byte)) = some [] := by
  rw [read_bytes_map_eq]
  simp [len_word, word_to_nat, read_bytes_aux]

/-- The EFAULT gate is off when the readable prefix has the full
    (arbitrary) length: it reduces to [negb b && b]. -/
theorem negb_andb_diag (b : Bool) : (!b && b) = false := by
  cases b <;> rfl

/-- A fully readable iovec sequence's gatherable prefix is the whole
    flattening... -/
theorem gather_prefix_full (mp : word → Option byte) (iovs : List (word × word)) (bs : List byte)
    (Hg : gather_iovecs mp iovs = some bs) : gather_prefix mp iovs = bs := by
  induction iovs generalizing bs with
  | nil =>
    simp [gather_iovecs] at Hg
    subst Hg
    simp [gather_prefix]
  | cons hd r ih =>
    obtain ⟨base, len⟩ := hd
    simp only [gather_iovecs] at Hg
    cases hw : read_bytes_map mp base len with
    | none =>
      rw [hw] at Hg
      exact nomatch Hg
    | some w =>
      rw [hw] at Hg
      cases hr : gather_iovecs mp r with
      | none =>
        rw [hr] at Hg
        exact nomatch Hg
      | some rest =>
        rw [hr] at Hg
        simp only [Option.some.injEq] at Hg
        subst Hg
        simp only [gather_prefix]
        have hfull : readable_bytes mp base len = w := readable_bytes_full mp base len w hw
        have hlen : ((w.length : Int)) = (len.toNat : Int) :=
          read_bytes_map_length mp base len w hw
        rw [hfull, ite_eq_left hlen, ih (bs := rest) hr]

/-- ...of the full requested length. -/
theorem gather_iovecs_length (mp : word → Option byte) (iovs : List (word × word)) (bs : List byte)
    (Hg : gather_iovecs mp iovs = some bs) : (bs.length : Int) = iovs_total iovs := by
  induction iovs generalizing bs with
  | nil =>
    simp [gather_iovecs] at Hg
    subst Hg
    simp [iovs_total]
  | cons hd r ih =>
    obtain ⟨base, len⟩ := hd
    simp only [gather_iovecs] at Hg
    cases hw : read_bytes_map mp base len with
    | none =>
      rw [hw] at Hg
      exact nomatch Hg
    | some w =>
      rw [hw] at Hg
      cases hr : gather_iovecs mp r with
      | none =>
        rw [hr] at Hg
        exact nomatch Hg
      | some rest =>
        rw [hr] at Hg
        simp only [Option.some.injEq] at Hg
        subst Hg
        simp only [iovs_total]
        have hlen : ((w ++ rest).length : Int) = (w.length : Int) + (rest.length : Int) := by
          rw [List.length_append]
          push_cast
          rfl
        rw [hlen, read_bytes_map_length mp base len w hw, ih (bs := rest) hr]

/-- [alloc_fd] scans at most 4096 candidates starting at 0, so its result
    is at most 4096 — far below the error-encoding range
    [2^64-4095, 2^64), so a successful open's return is never confused
    with an errno. -/
def check_ret_only (eff : SyscallEffect) (r : word) (m' : Model)
    (evs : List event) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if bv_eqb ret r then .CheckOk m' evs else .CheckReject
  | _ => .CheckReject

def access_ranges_eqb : List (word × Nat) → List (word × Nat) → Bool
  | [], [] => true
  | (a, n) :: xs', (b, k) :: ys' =>
      bv_eqb a b && (n == k) && access_ranges_eqb xs' ys'
  | _, _ => false

theorem access_ranges_eqb_eq (xs ys : List (word × Nat)) :
    access_ranges_eqb xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [access_ranges_eqb]
  | cons hd r ih =>
    obtain ⟨a, n⟩ := hd
    cases ys with
    | nil => simp [access_ranges_eqb]
    | cons hd2 r2 =>
      obtain ⟨b, k⟩ := hd2
      simp [access_ranges_eqb, Bool.and_eq_true, Fs.bv_eqb_eq, beq_iff_eq, ih]

theorem access_ranges_eqb_refl (xs : List (word × Nat)) :
    access_ranges_eqb xs xs = true :=
  (access_ranges_eqb_eq xs xs).mpr rfl

def clear_copyins (eff : SyscallEffect) : SyscallEffect :=
  with_copyins [] eff

def check_ret_only_copyins (reads : List (word × Nat))
    (eff : SyscallEffect) (r : word) (m' : Model) (evs : List event)
    : check_result :=
  match check_ret_only (clear_copyins eff) r m' evs with
  | .CheckOk m'' evs' =>
      if access_ranges_eqb eff.eff_copyins reads
      then .CheckOk m'' evs'
      else .CheckReject
  | result => result

def check_copyins (reads : List (word × Nat)) (eff : SyscallEffect)
    (result : check_result) : check_result :=
  if access_ranges_eqb eff.eff_copyins reads then result else .CheckReject

def strip_copyin_prefix (reads : List (word × Nat))
    (eff : SyscallEffect) : SyscallEffect :=
  with_copyins (eff.eff_copyins.drop reads.length) eff

def check_copyin_prefix (reads : List (word × Nat))
    (eff : SyscallEffect) (result : check_result) : check_result :=
  match result with
  | .CheckUnmodeled => .CheckUnmodeled
  | result' =>
      if access_ranges_eqb (eff.eff_copyins.take reads.length) reads
      then result'
      else .CheckReject

/- -------------------------------------------------- pathname copy-ins

   A spec whose body performs a single pathname read and no later
   copy-in records that one range with [Syscall.record_copyins].  These
   relate such a spec to its checker: the checker decides the body
   against the effect with its ledger CLEARED, then requires the claimed
   ledger to equal exactly that range.  [CheckUnmodeled] passes straight
   through — the model left the modeled surface, so it makes no claim
   about what was copied.  Two consumers: [Fs.Open.check_openat]
   and [Fs.Namei.check_unlinkat]. -/
def check_copyins_after (reads : List (word × Nat))
    (eff : SyscallEffect) (result : check_result) : check_result :=
  match result with
  | .CheckUnmodeled => .CheckUnmodeled
  | result' => check_copyins reads eff result'

theorem check_copyins_after_ok_iff (reads : List (word × Nat)) (eff : SyscallEffect)
    (result : check_result) (m : Model) (evs : List event) :
    check_copyins_after reads eff result = .CheckOk m evs ↔
      eff.eff_copyins = reads ∧ result = .CheckOk m evs := by
  cases result with
  | CheckOk m' evs' =>
    unfold check_copyins_after check_copyins
    try dsimp only
    by_cases h : access_ranges_eqb eff.eff_copyins reads = true
    · have hreads : eff.eff_copyins = reads := (access_ranges_eqb_eq _ _).mp h
      rw [ite_eq_left h, hreads]
      simp
    · rw [ite_eq_right h]
      constructor
      · intro hc
        exact nomatch hc
      · rintro ⟨hreads, -⟩
        exact False.elim (h (by rw [hreads]; exact access_ranges_eqb_refl reads))
  | CheckReject =>
    simp [check_copyins_after, check_copyins]
  | CheckUnmodeled =>
    simp [check_copyins_after]

theorem check_copyins_after_unmodeled (reads : List (word × Nat)) (eff : SyscallEffect)
    (result : check_result) (H : check_copyins_after reads eff result = .CheckUnmodeled) :
    result = .CheckUnmodeled := by
  cases result with
  | CheckOk m evs =>
    unfold check_copyins_after check_copyins at H
    try dsimp only at H
    by_cases h : access_ranges_eqb eff.eff_copyins reads = true
    · rw [ite_eq_left h] at H
      exact nomatch H
    · rw [ite_eq_right h] at H
      exact nomatch H
  | CheckReject =>
    unfold check_copyins_after check_copyins at H
    try dsimp only at H
    by_cases h : access_ranges_eqb eff.eff_copyins reads = true
    · rw [ite_eq_left h] at H
      exact nomatch H
    · rw [ite_eq_right h] at H
      exact nomatch H
  | CheckUnmodeled => rfl

theorem record_copyins_clear_ok (reads : List (word × Nat)) (spec : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hreads : eff.eff_copyins = reads)
    (Hspec : spec i m (.ok (clear_copyins eff) m' evs)) :
    record_copyins reads spec i m (.ok eff m' evs) := by
  have hEff : eff = with_copyins reads (clear_copyins eff) := by
    obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
    simp only [clear_copyins, with_copyins] at Hreads ⊢
    subst Hreads
    rfl
  rw [hEff]
  exact record_copyins_ok_empty rfl Hspec

theorem input_bind_ok_inv {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (x : A) (m' : Model) (evs : List event)
    (H : bind input k i m (.ok x m' evs)) : k i i m (.ok x m' evs) := by
  unfold LinuxSem.LinuxProcessSem.bind input at H
  obtain ⟨x0, m1, evs1, evs2, h1, h2, h3⟩ := H
  simp only [Outcome.ok.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  simp only [List.nil_append] at h3
  subst h3
  exact h2

theorem record_copyins_ok_inv (reads : List (word × Nat)) (spec : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : record_copyins reads spec i m (.ok eff m' evs)) :
    ∃ core, spec i m (.ok core m' evs) ∧
      eff = with_copyins (reads ++ core.eff_copyins) core := by
  unfold record_copyins LinuxSem.LinuxProcessSem.bind
    LinuxSem.LinuxProcessSem.pure at H
  obtain ⟨core, m1, evs1, evs2, Hcore, Hpure, Hevs⟩ := H
  simp only [Outcome.ok.injEq] at Hpure
  obtain ⟨hEff, hm, hevs2⟩ := Hpure
  subst hevs2
  subst hm
  have Hevs' : evs = evs1 := by simpa using Hevs
  subst Hevs'
  exact ⟨core, Hcore, hEff⟩

theorem input_bind_unmodeled_inv {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (H : bind input k i m .unmodeled) :
    k i i m .unmodeled := by
  unfold LinuxSem.LinuxProcessSem.bind input at H
  rcases H with h | ⟨x, m1, evs1, h1, h2⟩
  · exact nomatch h
  · simp only [Outcome.ok.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact h2

/-- The same two, for the [get_model] a spec reads right after its
    input.  [Fs.Namei.unlinkat_spec] opens with both because its flag
    test precedes the copy-in it records, so the two binds sit outside
    the [record_copyins] rather than inside it. -/
theorem get_model_bind_ok_inv {A : Type} (k : Model → SysSpec A)
    (i : SyscallInput) (m : Model) (x : A) (m' : Model) (evs : List event)
    (H : bind getModel k i m (.ok x m' evs)) : k m i m (.ok x m' evs) := by
  unfold LinuxSem.LinuxProcessSem.bind getModel at H
  obtain ⟨m0, m1, evs1, evs2, h1, h2, h3⟩ := H
  simp only [Outcome.ok.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  simp only [List.nil_append] at h3
  subst h3
  exact h2

theorem get_model_bind_unmodeled_inv {A : Type} (k : Model → SysSpec A)
    (i : SyscallInput) (m : Model) (H : bind getModel k i m .unmodeled) :
    k m i m .unmodeled := by
  unfold LinuxSem.LinuxProcessSem.bind getModel at H
  rcases H with h | ⟨m0, m1, evs1, h1, h2⟩
  · exact nomatch h
  · simp only [Outcome.ok.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact h2

theorem record_copyins_unmodeled_inv (reads : List (word × Nat)) (spec : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (H : record_copyins reads spec i m .unmodeled) :
    spec i m .unmodeled := by
  unfold record_copyins LinuxSem.LinuxProcessSem.bind
    LinuxSem.LinuxProcessSem.pure at H
  rcases H with h | ⟨core, m1, evs1, h1, h2⟩
  · exact h
  · exact nomatch h2

/-- The one-reader peel for [input], the two-outcome form of
    [input_bind_ok_inv]/[input_bind_unmodeled_inv]. -/
private theorem input_bind_inv {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event)
    (H : bind input k i m o) : k i i m o := by
  cases o with
  | ok x m' evs => exact input_bind_ok_inv k i m x m' evs H
  | unmodeled => exact input_bind_unmodeled_inv k i m H

/-- Peel an [i <- input ;; m <- get_model ;; ...] prologue.  Both
    readers step to the syscall's own model and input emitting nothing,
    so an outcome of the pair is an outcome of the body — and unlike
    [inv_ok], this keeps the body's hypothesis under a name a later step
    can still pass to another lemma.  Both [recvfrom_spec] and
    [socketpair_spec] open this way, in this order. -/
theorem bind_input_model_inv {A : Type} (k : SyscallInput → Model → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event)
    (H : bind input (fun i0 => bind getModel (fun m0 => k i0 m0)) i m o) :
    k i m i m o := by
  have h1 : bind getModel (fun m0 => k i m0) i m o :=
    input_bind_inv (fun i0 => bind getModel (fun m0 => k i0 m0)) i m o H
  exact (bind_getModel (fun m0 => k i m0) i m o).mp h1

/-- The one-reader case of the same peel, for an arm that opens with
    [m <- get_model ;; ...] alone. -/
theorem bind_model_inv {A : Type} (k : Model → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event)
    (H : bind getModel k i m o) : k m i m o :=
  (bind_getModel k i m o).mp H

/-- [Uaccess.access_ok_zero] as an acceptor: when the kernel moved no
    bytes, the range verdict is all that is left, so either the arm's
    own zero answer stands, or the only admissible return is -EFAULT, or
    the model declines. -/
def eff_is_errno (code : Int) (eff : SyscallEffect) : Bool :=
  match eff with
  | ⟨r, [], [], [], [], []⟩ => bv_eqb r (errno_ret code)
  | _ => false

/- ---------------------------------------------------------------- tactics

   Three small rewrite tactics, plus two more below ([bool_true],
   [inv_ok]) and the spec unfolder [sys_unfold].  Each is
   `rw`/`dsimp`/`simp`/`rcases` under a name the checkers below cite. -/

/-- Rewrite an equation and re-reduce everything. -/
macro "srw " e:term : tactic => `(tactic| (simp only [$e:term]; try dsimp only))

/-- [srw] under one hypothesis. -/
macro "hrw " e:term " in " h:ident : tactic =>
  `(tactic| (simp only [$e:term] at $h:ident; try dsimp only at $h:ident))

/-- Rewrite an equation wherever it applies and re-reduce everything —
    used when [inv_ok] has already renamed the interesting hypothesis. -/
macro "hall " e:term : tactic =>
  `(tactic| (try simp only [$e:term] at *; try dsimp only at *))

theorem error_b_big (r : word) (H : addr_is_error_b r = true) :
    (18446744073709547520 : Int) < (r.toNat : Int) := by
  unfold addr_is_error_b at H
  rw [decide_eq_true_eq] at H
  unfold two_pow_64 at H
  omega

/-- Discharge a boolean side condition: `bv_eqb` reflexivity, equations
    from the context, and the decidable comparisons. -/
macro "bool_true" : tactic =>
  `(tactic| (simp only [bv_eqb, beq_iff_eq, decide_eq_true_eq] at *
             repeat (first
               | rw [bv_eqb_refl]
               | assumption
               | omega)))

/-- [bind_ok] with the event concatenation as an explicit equation. -/
theorem bind_ok_eq {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (x : A) (m1 : Model) (evs1 : List event)
    (y : B) (m2 : Model) (evs2 evs : List event)
    (Hc : c i m (.ok x m1 evs1)) (Hk : k x i m1 (.ok y m2 evs2))
    (Hevs : evs = evs1 ++ evs2) :
    bind c k i m (.ok y m2 evs) := by
  subst Hevs
  exact bind_ok c k i m x m1 evs1 y m2 evs2 Hc Hk

/-- [bind_ok] specialised to a first component that emits no events —
    every reader/state accessor in the DSL.  (Plain [bind_ok] cannot be
    [eapply]ed against a CONCRETE event list: [?evs1 ++ ?evs2] does not
    unify with it.) -/
theorem bind_ok0 {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (x : A) (m1 : Model) (y : B) (m2 : Model)
    (evs : List event)
    (Hc : c i m (.ok x m1 [])) (Hk : k x i m1 (.ok y m2 evs)) :
    bind c k i m (.ok y m2 evs) := by
  have h := bind_ok c k i m x m1 [] y m2 evs Hc Hk
  simpa using h

theorem check_ret_only_ok_iff (eff : SyscallEffect) (r : word) (m1 : Model) (evs1 : List event)
    (m' : Model) (evs : List event) :
    check_ret_only eff r m1 evs1 = .CheckOk m' evs ↔
      (eff = mkEffect r [] [] ∧ m' = m1 ∧ evs = evs1) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [check_ret_only]
  · by_cases h : bv_eqb ret r = true
    · have hr : ret = r := (Fs.bv_eqb_eq ret r).mp h
      subst hr
      rw [ite_eq_left h]
      simp [mkEffect, check_result.CheckOk.injEq]
      exact ⟨fun hh => ⟨hh.1.symm, hh.2.symm⟩, fun hh => ⟨hh.1.symm, hh.2.symm⟩⟩
    · rw [ite_eq_right h]
      constructor
      · intro hc
        exact nomatch hc
      · rintro ⟨heff, -⟩
        have hret : ret = r := by
          have hc := congrArg SyscallEffect.eff_ret heff
          simpa [mkEffect] using hc
        exact False.elim (h (by rw [hret]; exact bv_eqb_refl r))
  all_goals simp [mkEffect]

/-- The ledger gate alone: an accepted outcome is exactly the claimed
    ledger plus the delivered model and events. -/
private theorem if_access_checkOk_iff (copyins reads : List (word × Nat))
    (m1 : Model) (evs1 : List event) (m' : Model) (evs : List event) :
    (if access_ranges_eqb copyins reads then check_result.CheckOk m1 evs1
        else check_result.CheckReject) = check_result.CheckOk m' evs ↔
      (copyins = reads ∧ m' = m1 ∧ evs = evs1) := by
  by_cases h : access_ranges_eqb copyins reads = true
  · have hreads : copyins = reads := (access_ranges_eqb_eq _ _).mp h
    rw [ite_eq_left h, hreads]
    simp [check_result.CheckOk.injEq]
    exact ⟨fun hh => ⟨hh.1.symm, hh.2.symm⟩, fun hh => ⟨hh.1.symm, hh.2.symm⟩⟩
  · rw [ite_eq_right h]
    constructor
    · intro hc
      exact nomatch hc
    · rintro ⟨hreads, -⟩
      exact False.elim (h (by rw [hreads]; exact access_ranges_eqb_refl reads))

theorem check_ret_only_copyins_ok_iff (reads : List (word × Nat)) (eff : SyscallEffect)
    (r : word) (m1 : Model) (evs1 : List event) (m' : Model) (evs : List event) :
    check_ret_only_copyins reads eff r m1 evs1 = .CheckOk m' evs ↔
      (eff = with_copyins reads (mkEffect r [] []) ∧ m' = m1 ∧ evs = evs1) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_ret_only_copyins clear_copyins with_copyins
  try dsimp only
  cases hcore : check_ret_only ⟨ret, ws, zs, us, cs, []⟩ r m1 evs1 with
  | CheckOk m'' evs' =>
    try dsimp only
    have Hcore := (check_ret_only_ok_iff ⟨ret, ws, zs, us, cs, []⟩ r m1 evs1 m'' evs').mp hcore
    obtain ⟨hclear, hm'', hevs'⟩ := Hcore
    have hcomp : ret = r ∧ ws = [] ∧ zs = [] ∧ us = [] ∧ cs = [] := by
      have hh := hclear
      simp only [mkEffect, SyscallEffect.mkEffectU.injEq, and_true] at hh
      exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩
    obtain ⟨hret, hws, hzs, hus, hcs⟩ := hcomp
    subst hret
    subst hws
    subst hzs
    subst hus
    subst hcs
    subst hm''
    subst hevs'
    try dsimp only
    rw [if_access_checkOk_iff]
    simp
  | CheckReject =>
    try dsimp only
    constructor
    · intro hc
      exact nomatch hc
    · rintro ⟨heff, -⟩
      have hcomp : ret = r ∧ ws = [] ∧ zs = [] ∧ us = [] ∧ cs = [] ∧ copyins = reads := by
        simpa [with_copyins, mkEffect, SyscallEffect.mkEffectU.injEq] using heff
      obtain ⟨hret, hws, hzs, hus, hcs, -⟩ := hcomp
      rw [hret, hws, hzs, hus, hcs] at hcore
      have hok := (check_ret_only_ok_iff ⟨r, [], [], [], [], []⟩ r m1 evs1 m1 evs1).mpr
        ⟨rfl, rfl, rfl⟩
      rw [hok] at hcore
      exact nomatch hcore
  | CheckUnmodeled =>
    try dsimp only
    constructor
    · intro hc
      exact nomatch hc
    · rintro ⟨heff, -⟩
      have hcomp : ret = r ∧ ws = [] ∧ zs = [] ∧ us = [] ∧ cs = [] ∧ copyins = reads := by
        simpa [with_copyins, mkEffect, SyscallEffect.mkEffectU.injEq] using heff
      obtain ⟨hret, hws, hzs, hus, hcs, -⟩ := hcomp
      rw [hret, hws, hzs, hus, hcs] at hcore
      have hok := (check_ret_only_ok_iff ⟨r, [], [], [], [], []⟩ r m1 evs1 m1 evs1).mpr
        ⟨rfl, rfl, rfl⟩
      rw [hok] at hcore
      exact nomatch hcore

theorem check_ret_only_no_unmodeled (eff : SyscallEffect) (r : word) (m1 : Model)
    (evs1 : List event) : check_ret_only eff r m1 evs1 ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [check_ret_only] <;>
    by_cases h : bv_eqb ret r = true <;> simp [h]

theorem check_ret_only_copyins_no_unmodeled (reads : List (word × Nat))
    (eff : SyscallEffect) (r : word) (m1 : Model) (evs1 : List event) :
    check_ret_only_copyins reads eff r m1 evs1 ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_ret_only_copyins clear_copyins with_copyins
  try dsimp only
  cases hcore : check_ret_only ⟨ret, ws, zs, us, cs, []⟩ r m1 evs1 with
  | CheckUnmodeled =>
    exact absurd hcore (check_ret_only_no_unmodeled _ _ _ _)
  | CheckOk m'' evs' =>
    try dsimp only
    by_cases h : access_ranges_eqb copyins reads = true <;> simp [h]
  | CheckReject =>
    try dsimp only
    simp

theorem check_ret_only_copyins_refl (reads : List (word × Nat)) (r : word) (m : Model)
    (evs : List event) :
    check_ret_only_copyins reads (with_copyins reads (mkEffect r [] [])) r m evs
      = .CheckOk m evs := by
  unfold check_ret_only_copyins clear_copyins with_copyins mkEffect
  try dsimp only
  have hok : check_ret_only ⟨r, [], [], [], [], []⟩ r m evs = .CheckOk m evs := by
    simp [check_ret_only, bv_eqb_refl]
  rw [hok]
  simp [access_ranges_eqb_refl]

/-- Decompose monadic hypotheses (after the combinators are unfolded):
    invert a constructor equality ([Ok] vs [Ok], [CheckOk] vs [CheckOk],
    [some] vs [some]), substitute what that yields, and split one
    conjunction.

    Lean has no [match goal], and the generic hypothesis selectors
    ([‹∃ _, _›], [‹_ ∨ _›]) elaborate their holes against the goal and
    loop, so this keeps the steps that are both safe and terminating: [simp] with the constructor
    injectivities, [subst_vars], and ONE conjunction split.  A checker
    that needs existentials, disjunctions or a second level spells them
    out with [rcases]/[obtain] at the call site. -/
macro "inv_ok" : tactic =>
  `(tactic| (try simp only [Outcome.ok.injEq, check_result.CheckOk.injEq,
      Option.some.injEq] at *
             try subst_vars
             try (rcases ‹_ ∧ _› with ⟨_, _⟩)))

/-- Unfold the monadic sugar of a spec down to the primitive combinators
    (sugar first, primitive combinators last, so everything bottoms out).

    The per-syscall state setters
    (`set_fds`, `set_pipes`, `set_vmmaps`, `add_vm_lazy`,
    `forget_vm_range`, `set_stdin`, `set_urandom`, `set_fs`, `set_halted`,
    `set_tid`, `set_rlimit_core`, `set_utsname`, `set_statpin`,
    `set_setsid_succeeded`, `set_clock`, `set_creds`, `set_sigmask`,
    `set_sigaltstack_installed`, `set_sigmask_deliver`,
    `set_sigabrt_pending`, `set_killed`, `get_fds`, `get_vmmaps`) are LOCAL
    helpers of the spec file that defines them rather than one global
    accessor matrix over `Model`, so no module can name them all; a checker
    under `Checks/` unfolds the ones its own arm uses with a file-local
    `simp only [...]`.  Everything that IS global is unfolded here. -/
macro "sys_unfold" : tactic =>
  `(tactic| simp only [
      LinuxSem.LinuxProcessSem.Sys.Syscall.record_copyins,
      with_copyins,
      LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
      LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
      LinuxSem.LinuxProcessSem.Sys.Syscall.errno_from,
      LinuxSem.LinuxProcessSem.Sys.Fs.File.lowest_fd,
      LinuxSem.LinuxProcessSem.getModel,
      LinuxSem.LinuxProcessSem.modify,
      LinuxSem.LinuxProcessSem.input,
      LinuxSem.LinuxProcessSem.sysno,
      LinuxSem.LinuxProcessSem.arg,
      LinuxSem.LinuxProcessSem.bind,
      LinuxSem.LinuxProcessSem.pure,
      LinuxSem.LinuxProcessSem.choose,
      LinuxSem.LinuxProcessSem.alt,
      LinuxSem.LinuxProcessSem.unmodeled,
      LinuxSem.LinuxProcessSem.emit] at *)

/- Bridges for the channel short-write acceptors: the claimed return
   decodes to the delivered prefix's length. -/

theorem len_word_unsigned {A : Type} (l : List A)
    (Hl : (l.length : Int) < two_pow_64) :
    ((len_word l).toNat : Int) = (l.length : Int) := by
  unfold len_word
  rw [BitVec.toNat_ofNat l.length 64]
  have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
  have hlt : l.length < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt]

theorem firstn_length_le_Z {A : Type} (l : List A) (r : Int)
    (H0 : 0 ≤ r) (Hle : r ≤ (l.length : Int)) :
    ((l.take r.toNat).length : Int) = r := by
  rw [List.length_take]
  have hle : r.toNat ≤ l.length := Int.toNat_le.mpr Hle
  rw [Nat.min_eq_left hle, Int.toNat_of_nonneg H0]

/-- The delivered prefix's [len_word] is the return value that selected
    it — the step every short-write site would otherwise re-derive. -/
theorem len_word_firstn_ret (ret : word) {A : Type} (l : List A)
    (H : 0 ≤ (ret.toNat : Int) ∧ (ret.toNat : Int) ≤ (l.length : Int)) :
    len_word (l.take ret.toNat) = ret := by
  have hlen : (l.take ret.toNat).length = ret.toNat := by
    rw [List.length_take]
    have hle : ret.toNat ≤ l.length := Int.toNat_le.mpr H.2
    rw [Nat.min_eq_left hle]
  unfold len_word
  rw [hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/- ------------------------------------------------------------------ read -/

theorem neq_einval_of_not_error (r : word) (H : addr_is_error_b r = false) :
    bv_eqb (errno_ret EINVAL) r = false := by
  cases h : bv_eqb (errno_ret EINVAL) r with
  | false => rfl
  | true =>
    exfalso
    have hr : errno_ret EINVAL = r := (Fs.bv_eqb_eq _ _).mp h
    rw [← hr] at H
    have h22 : 1 ≤ EINVAL ∧ EINVAL ≤ 4095 := by unfold EINVAL; decide
    rw [errno_ret_error_b EINVAL h22.1 h22.2] at H
    exact nomatch H

theorem eff_is_errno_true (code : Int) (eff : SyscallEffect)
    (H : eff_is_errno code eff = true) :
    eff = mkEffect (errno_ret code) [] [] := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [eff_is_errno] at H
  · have hr : ret = errno_ret code := (Fs.bv_eqb_eq ret (errno_ret code)).mp H
    subst hr
    rfl
  all_goals exact nomatch H

/-! ## The tactics' smoke tests -/

example (a b : word) (h : a = b) : bv_eqb a b = true := by bool_true

example (x y : Nat) (h : x = y) (g : x + 1 = 3) : y + 1 = 3 := by
  hall h
  exact g

example (x y : Nat) (h : x = y) (g : x + 1 = 3) : y + 1 = 3 := by
  hrw h in g
  exact g

example (x y : Nat) (h : x = y) : x + 1 = y + 1 := by srw h

example (p q : Prop) (h : p ∧ q) : q := by
  inv_ok
  assumption

example (r : word) :
    LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r =
      LinuxSem.LinuxProcessSem.pure (mkEffect r [] []) := by
  sys_unfold
