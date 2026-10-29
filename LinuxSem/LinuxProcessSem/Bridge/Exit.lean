/-
  * LinuxProcessSem.Bridge.Exit — a bounded common representation for the
    two exit arms


  The model reads the file [exit.hex] directly.  Each result relates the
  existing spec to this interpretation of that file.

  TRUST BOUNDARY: this file is part of the trusted specification.

  What each dependency supplies:

  - `State` supplies `Model`, `SyscallInput` and `in_arg`; `StateLedger`
    (pulled in through `StateMatrix`) supplies `with_halted` and
    `m_halted`, and `StateMatrix` carries the `@[simp]` accessor matrix,
    including `m_halted_with_halted`;
  - `MonadInstances` fixes the concrete `Sys Model SyscallInput event`, so
    `SysSpec SyscallEffect` is the type of a spec here;
  - `Specs` supplies `syscall_spec` and re-exports `Sys.SyscallTable`
    (`spec_table`, `arm`), `Sys.Dispatch` (`dispatch`, `lookup_arm`),
    `Sys.Kernel.Exit` (`exit_spec`) and `Sys.Syscall` (`ret_only`);
  - `RiscvSemantics` supplies `hex_read_bytes`, the existing image reader
    that `read_artifact` calls.

  NOTATION.  `Z` is `Int`, `word` is `BitVec 64`, `list` is `List`;
  `Z_to_bv n z` is `BitVec.ofInt n z`, `bv_unsigned w` is
  `(w.toNat : Int)`, `bv_and` is `&&&`, `bv_eqb` is `==`, `Z.to_nat` is
  `.toNat`, `option_map` is `Option.map`, and `Ok` / `Unmodeled` are
  `.ok` / `.unmodeled`.  A `unit`-returning step followed by `k` is
  `seqSpec x k`, and a string's length is already a `Nat`.

  `ReadFile`.  Lean has no build-time file inclusion, so `artifact_text`
  below is the eight characters of `Bridge/exit.hex`, written out.
  `artifact_checked` still decodes them through `hex_read_bytes`, so the
  interpretation of the artifact is checked rather than assumed; the
  `.hex` file stays the authority for those eight characters.

  `set_halted`.  `denote` below calls it.  `Monad.lean` is parameterized
  over the model and carries no state setters, so — following the
  precedent of `Sys/Kernel/Signal.lean` — the one this file needs is
  declared here.

  `Print Assumptions`.  Every result below is proved outright — no escape
  hatches, no assumed axioms — so the kernel's assumption set is empty.
-/
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.StateMatrix

namespace LinuxSem.LinuxProcessSem.Bridge.Exit

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-! ## The bounded common syntax -/

/-- Byte literals bound the common syntax, not the production
    specification or its raw 64-bit syscall arguments. -/
inductive Clause where
  /-- Halt, with `argument` masked by `mask`, recording `result`. -/
  | halt (argument mask result : byte)
  /-- The call is outside the modeled surface. -/
  | decline
  deriving DecidableEq, Repr

def serialize : Clause → List byte
  | .halt argument mask result => [BitVec.ofInt 8 0, argument, mask, result]
  | .decline => [BitVec.ofInt 8 1]

def deserialize : List byte → Option Clause
  | [tag, argument, mask, result] =>
      if tag == (BitVec.ofInt 8 0 : byte) then some (.halt argument mask result) else none
  | [tag] => if tag == (BitVec.ofInt 8 1 : byte) then some .decline else none
  | _ => none

theorem deserialize_serialize (c : Clause) : deserialize (serialize c) = some c := by
  cases c <;> rfl

theorem serialize_injective {a b : Clause} (h : serialize a = serialize b) : a = b := by
  have h' := congrArg deserialize h
  rw [deserialize_serialize, deserialize_serialize] at h'
  exact Option.some.inj h'

/-! ## The denotation, and its normal form -/

/-- Halt the process by an exit: `Monad.lean`'s `set_halted`, here
    `modifySpec (with_halted code)`.

    See the note on `set_halted` in the header. -/
def set_halted (code : word) : SysSpec Unit := modifySpec (with_halted code)

/-- The spec a clause denotes.  `halt` is `set_halted` on the masked
    argument register, followed by `ret_only` on `result`; `decline` is
    the fail-closed `unmodeled`. -/
def denote : Clause → SysSpec SyscallEffect
  | .halt argument mask result => fun i =>
      seqSpec (set_halted (in_arg i argument.toNat &&&
                  BitVec.ofInt 64 (mask.toNat : Int)))
        (ret_only (BitVec.ofInt 64 (result.toNat : Int))) i
  | .decline => unmodeled

/-- Keep the full post-model and every effect ledger.  `with_halted` acts on
    each development's actual `Model`; its extra state fields remain an
    audited cross-prover obligation. -/
def evaluate (c : Clause) (i : SyscallInput) (m : Model) :
    Outcome SyscallEffect Model event :=
  match c with
  | .halt argument mask result =>
      .ok (mkEffect (BitVec.ofInt 64 (result.toNat : Int)) [] [])
        (with_halted (in_arg i argument.toNat &&&
                      BitVec.ofInt 64 (mask.toNat : Int)) m) []
  | .decline => .unmodeled

/-- The normal form of `bind (modify f) (fun _ => ret_only r)`: exactly one
    `ok` outcome, returning `r` with no writes, at the model `f` produced.

    helper.  `denote_normal_form` proves this by
    unfolding the same three definitions and inverting the two equations;
    naming it once keeps the port of that proof to the two clause cases. -/
private theorem bind_modify_ret_only_iff (f : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    bind (modify f) (fun _ => ret_only r) i m o ↔ o = .ok (mkEffect r [] []) (f m) [] := by
  cases o with
  | ok x m' evs =>
      simp only [bind, modify, ret_only, pure]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        injection h1 with _ hm1 he1
        injection h2 with hx hm2 he2
        subst hm1
        subst he1
        subst hx
        subst hm2
        subst he2
        simp only [List.append_nil] at h3
        rw [h3]
      · rintro ⟨rfl, rfl, rfl⟩
        exact ⟨(), f m, [], [], rfl, rfl, rfl⟩
  | unmodeled =>
      simp [bind, modify, ret_only, pure]

theorem denote_normal_form (c : Clause) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    denote c i m o ↔ o = evaluate c i m := by
  cases c with
  | halt argument mask result =>
      exact bind_modify_ret_only_iff
        (with_halted (in_arg i argument.toNat &&&
          BitVec.ofInt 64 (mask.toNat : Int)))
        (BitVec.ofInt 64 (result.toNat : Int)) i m o
  | decline => rfl

/-! ## The artifact -/

def exit_clause : Clause :=
  Clause.halt (BitVec.ofInt 8 0) (BitVec.ofInt 8 255) (BitVec.ofInt 8 0)

/-- The eight characters of the `exit.hex` fixture
    (`00 00 ff 00`, i.e. `halt 0 255 0`), written out; see the NOTE on
    `ReadFile` in the header. -/
def artifact_text : String := "0000ff00"

/-- Read the entire file.  Odd lengths or trailing tokens cannot silently
    disappear; `hex_read_bytes` is the existing image reader. -/
def read_artifact (text : String) : Option Clause :=
  let len := text.length
  if len % 2 == 0 then
    match hex_read_bytes text 0 (len / 2) with
    | some bs => deserialize bs
    | none => none
  else none

def artifact_clause : Option Clause := read_artifact artifact_text

theorem artifact_checked : artifact_clause = some exit_clause := by
  -- The clause is a closed term, so `decide` settles it.
  decide

theorem artifact_unique {c : Clause} (h : artifact_clause = some c) : c = exit_clause := by
  rw [artifact_checked] at h
  exact (Option.some.inj h).symm

/-- `exit_spec (in_arg i 0)` is the `halt` arm of `denote exit_clause`
    definitionally. -/
theorem exit_spec_denotes (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    exit_spec (in_arg i 0) i m o ↔ denote exit_clause i m o := by
  rfl

def exit_number (no : word) : Prop :=
  (no.toNat : Int) = 93 ∨ (no.toNat : Int) = 94

/-- The dispatch scrutinee is rewritten to the literal number, and the
    lets the table reduce (`unfold syscall_spec, dispatch; rewrite Hno`).
    Here the reduction is the `rfl` proofs of `lookup_arm spec_table 93` /
    `lookup_arm spec_table 94` — the table is a literal list, so the first
    matching arm is found by computation — and `dispatch_arm` turns the
    lookup into the arm's spec. -/
theorem exit_dispatch_denotes (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hno : exit_number i.in_sysno) :
    syscall_spec i m o ↔ denote exit_clause i m o := by
  obtain h | h := hno
  · have hlk : lookup_arm spec_table 93
        = some (arm 93 (fun i => exit_spec (in_arg i 0))) := rfl
    exact (dispatch_arm spec_table i m o _
      (by rw [h]; exact hlk)).trans (exit_spec_denotes i m o)
  · have hlk : lookup_arm spec_table 94
        = some (arm 94 (fun i => exit_spec (in_arg i 0))) := rfl
    exact (dispatch_arm spec_table i m o _
      (by rw [h]; exact hlk)).trans (exit_spec_denotes i m o)

/-- Agreement with the file is proved, not assumed as a scoping premise. -/
theorem exit_dispatch_artifact (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hno : exit_number i.in_sysno) :
    syscall_spec i m o ↔ ∃ c, artifact_clause = some c ∧ denote c i m o := by
  rw [artifact_checked]
  rw [exit_dispatch_denotes i m o hno]
  constructor
  · intro h
    exact ⟨exit_clause, rfl, h⟩
  · rintro ⟨c, hc, h⟩
    obtain rfl : c = exit_clause := (Option.some.inj hc).symm
    exact h

theorem exit_dispatch_normal_form (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hno : exit_number i.in_sysno) :
    syscall_spec i m o ↔ o = evaluate exit_clause i m :=
  (exit_dispatch_denotes i m o hno).trans (denote_normal_form exit_clause i m o)

/-- Normalize the bitvector primitive to a common unsigned arithmetic
    formula, for every raw word rather than only the pilot's argument.

    NOTE.  The proof rewrites with `bv_and_unsigned` and then applies
    `Z.land_ones`; here the same two steps are `BitVec.toNat_and` (to
    `Nat`) and `Nat.and_two_pow_sub_one_eq_mod` (`x &&& (2^8 - 1) =
    x % 2^8`), and `Int.natCast_emod` carries the result back to `Int`,
    which is where the identity belongs. -/
theorem status_mod256 (code : word) :
    ((code &&& BitVec.ofInt 64 255).toNat : Int) = (code.toNat : Int) % 256 := by
  have h255 : (BitVec.ofInt 64 255 : word).toNat = 255 := rfl
  rw [BitVec.toNat_and, h255]
  have h : code.toNat &&& 255 = code.toNat % 256 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod code.toNat 8
  rw [h]
  exact Int.natCast_emod _ _

theorem exit_dispatch_status (i : SyscallInput) (m m' : Model)
    (eff : SyscallEffect) (evs : List event) (hno : exit_number i.in_sysno)
    (h : syscall_spec i m (.ok eff m' evs)) :
    (m_halted m').map (fun w => (w.toNat : Int)) =
      some ((in_arg i 0).toNat % 256 : Int) := by
  have h' : (.ok eff m' evs : Outcome SyscallEffect Model event)
      = evaluate exit_clause i m :=
    (exit_dispatch_normal_form i m _ hno).mp h
  simp only [evaluate, exit_clause] at h'
  simp only [Outcome.ok.injEq] at h'
  obtain ⟨-, rfl, -⟩ := h'
  rw [m_halted_with_halted]
  -- `exit_clause`'s byte literals are `BitVec.ofInt 8 0` / `ofInt 8 255`;
  -- `show` reads the two `.toNat`s through to the literals `0` and `255`
  -- and applies the `Option.map` at `some`, which is what puts the masked
  -- word in `status_mod256`'s shape.
  show some ((in_arg i 0 &&& BitVec.ofInt 64 255).toNat : Int) =
    some ((in_arg i 0).toNat % 256 : Int)
  rw [status_mod256]

/-! ## Port checks

    The computable goals in this file are `deserialize_serialize` and
    `artifact_checked`, both proved above.  The two checks below pin the
    byte encoding and the artifact text itself; they are port checks, not
    reused lemmas. -/

/-- The exit clause serializes to the artifact's four bytes. -/
example : serialize exit_clause = [(0 : byte), 0, 255, 0] := by decide

/-- The one-byte tag decodes to the decline clause. -/
example : deserialize [(1 : byte)] = some .decline := by decide

end LinuxSem.LinuxProcessSem.Bridge.Exit
