/-
  * LinuxSem.Checks.Cases.Kernel.Fork — worked examples over set_tid_address (96)

  Worked cases over `Sys.Kernel.Fork`, which answers to Linux [kernel/fork.c]: the
  examples for the syscalls defined there, and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names; the few spellings Lean does
  not have are supplied as local transparent `abbrev`s below,
  DEFINITIONALLY EQUAL to what they stand for:
  - `bv_unsigned w` is `(w.toNat : Int)`;
  - a chained comparison `0 < a < b` is written `0 < a ∧ a < b`.

  Proofs.  The one lemma here is quantified over free variables, so it
  carries an ordinary tactic proof.  The shape: the spec hypothesis is
  inverted with `check_set_tid_address_complete_ok` (a `have`), the
  effect is destructed field by field with `obtain`/`cases` (each cons
  case is a `nomatch` on the `CheckReject` arm), and a `CheckOk` equation
  is inverted with `check_result.CheckOk.inj`.  The `Bool` conjuncts come
  apart with `Bool.and_eq_true`, and a `zltb` fact becomes a proposition
  by `of_decide_eq_true`.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Fs.ReadWrite
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
import LinuxSem.Checks.Sys.Kernel.Fork

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Fork
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Kernel.Fork

/-! ## The prelude's abbreviations, restored

    Each of these is a transparent alias, so it
    changes no statement's meaning. -/

/-- `bv_unsigned` (`BvBase`): the unsigned value of a bitvector, in
    `Int` so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `Z_to_bv`: an `Int` re-wrapped at width `n`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `Z.eqb` (and `Nat.eqb`), over any `BEq`. -/
abbrev zeqb {α : Type} [BEq α] (a b : α) : Bool := a == b

/-- `Z.leb` on `Int`. -/
abbrev zleb (a b : Int) : Bool := decide (a ≤ b)

/-- `Z.ltb` on `Int`. -/
abbrev zltb (a b : Int) : Bool := decide (a < b)

/-! * LinuxProcessSem.Checks.Cases.Kernel.Fork — worked examples over set_tid_address (96)

    Worked cases over `Sys.Kernel.Fork`, which answers to Linux [kernel/fork.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/


theorem set_tid_address_first_choice_is_within_modeled_envelope :
  ∀ i m eff m' evs,
  m_tid m = none →
  set_tid_address_spec i m (.ok eff m' evs) →
  ∃ tid,
    (0 < bv_unsigned tid ∧ bv_unsigned tid < PID_MAX_ENVELOPE) ∧
    eff = mkEffect tid [] [] ∧
    m' = with_tid tid m ∧
    evs = []
:= by
  intro i m eff m' evs Htid Hspec
  have Hc := check_set_tid_address_complete_ok eff m m' evs i Hspec
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [check_set_tid_address] at Hc
  case nil.nil.nil.nil.nil =>
    rw [Htid] at Hc
    by_cases hv : (decide (0 < (ret.toNat : Int)) &&
        decide ((ret.toNat : Int) < PID_MAX_ENVELOPE)) = true
    · rw [ite_eq_left hv] at Hc
      obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj Hc
      have hv' := hv
      simp only [Bool.and_eq_true] at hv'
      exact ⟨ret, ⟨of_decide_eq_true hv'.1, of_decide_eq_true hv'.2⟩,
        rfl, rfl, rfl⟩
    · rw [ite_eq_right hv] at Hc
      cases Hc
  all_goals cases Hc


end LinuxSem.Checks.Cases.Kernel.Fork
