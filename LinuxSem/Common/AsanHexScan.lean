/-
  * Common.AsanHexScan — postulate-free check that every byte offset below
    a given count of a segment hex chunk decodes
    (`hex_byte_at s off <> none`).

  Driving the scan off a 63-bit cursor would need cast laws (`of_to_N`,
  `add_spec`, `leb_spec`, ...) relating the cursor to the spec's
  `hex_byte_at`, and any such postulate would show up in `#print axioms`.
  This scan simply EVALUATES the trusted spec's own `hex_byte_at s off` at
  every offset (binary-split recursion on the byte count, so no big unary
  numbers), hence its soundness lemma is purely structural: no 63-bit
  reasoning, nothing beyond Lean's own postulates.  Cost: about 5.4 M
  evaluations of `hex_byte_at` for the asan .bss chunk (seconds under
  kernel evaluation).

  NOTES (types).  The chunks are `String`s and the offsets `Nat` (see
  `RiscvSemantics`'s note on the hex helpers): `hex_byte_at` takes a `Nat`
  byte offset, halving is `n / 2`, the equality test is `==` on `Bool`, and
  the bound tests are `<`/`≤` on `Nat`.  `s.length` is already a character
  count, so `segment_byte_at`'s own `chunk.length / 2` is the same number
  the hypothesis below divides.

  NOTES (proofs).  `scanN_sound` is by induction on the fuel, with the
  `==` dispatches discharged by `simp` and all arithmetic (`i - h`,
  `base + h + (i - h) = base + i`, the `n = 1` collapse) by `omega`.  The
  casts in `segment_byte_at_some1` are the identity on the `Nat` side, so
  the hypothesis `(n <= (...))%N` is `n ≤ s.length / 2` and the offset test
  is `off < n`.

  NOTES (`#print axioms`).  Lean has no 63-bit cursor, so the cast
  postulates that would otherwise be needed cannot appear.  What
  `#print axioms` reports for `scanN_sound` / `segment_byte_at_some1` is
  `[propext, Classical.choice, Quot.sound]` — Lean's standard axioms.
  `Classical.choice` arrives through the STATEMENT's `String.length` (the
  core model of `String.toList` uses it), not through any step of these
  proofs: the induction, `omega` and `decide` contribute none of it, and
  this file adds no new postulate.
-/
import LinuxSem.LinuxProcessSem.RiscvSemantics

namespace LinuxSem.Common.AsanHexScan

open LinuxSem.LinuxProcessSem.RiscvSemantics

def byte_ok (s : String) (off : Nat) : Bool :=
  match hex_byte_at s off with
  | some _ => true
  | none => false

/-- `scanN s fuel base n` checks offsets `[base, base+n)` by binary splitting of `n`. -/
def scanN (s : String) (fuel : Nat) (base n : Nat) : Bool :=
  match fuel with
  | 0 => n == 0
  | f + 1 =>
      if n == 0 then true
      else if n == 1 then byte_ok s base
      else
        let h := n / 2
        scanN s f base h && scanN s f (base + h) (n - h)

theorem scanN_sound : ∀ (s : String) (fuel base n : Nat),
    scanN s fuel base n = true → ∀ i, i < n → hex_byte_at s (base + i) ≠ none := by
  intro s fuel
  induction fuel with
  | zero =>
    intro base n h i hi
    simp only [scanN] at h
    have hn : n = 0 := by simpa using h
    omega
  | succ f ih =>
    intro base n h i hi
    simp only [scanN] at h
    by_cases hn0 : n = 0
    · omega
    · have hbeq0 : (n == 0) = false := by simp [hn0]
      rw [hbeq0] at h
      simp only [Bool.false_eq_true, ite_false] at h
      by_cases hn1 : n = 1
      · subst hn1
        have hi0 : i = 0 := by omega
        subst hi0
        cases hb : hex_byte_at s base with
        | none => simp [byte_ok, hb] at h
        | some v => simp
      · have hbeq1 : (n == 1) = false := by simp [hn1]
        rw [hbeq1] at h
        simp only [Bool.false_eq_true, ite_false] at h
        rw [Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        rcases Nat.lt_or_ge i (n / 2) with hlt | hge
        · exact ih base (n / 2) h1 i hlt
        · have hstep : hex_byte_at s (base + n / 2 + (i - n / 2)) ≠ none :=
            ih (base + n / 2) (n - n / 2) h2 (i - n / 2) (by omega)
          rwa [show base + n / 2 + (i - n / 2) = base + i from by omega] at hstep

/-- Consequence for a one-chunk segment byte list: `chunk_bytes` is the spec's
    own length expression, which the image files evaluate once by `vm_compute`
    (pure computation, no axioms). -/
theorem segment_byte_at_some1 (s : String) (n off : Nat)
    (Hs : scanN s 64 0 n = true)
    (Hn : n ≤ s.length / 2)
    (Hoff : off < n) :
    segment_byte_at [s] off ≠ none := by
  have hoff : off < s.length / 2 := by omega
  have hunf : segment_byte_at [s] off = hex_byte_at s off := by
    simp [segment_byte_at, hoff]
  rw [hunf]
  simpa using scanN_sound s 64 0 n Hs off Hoff

/-! ## Sanity checks (decidable checks) -/

example : scanN "93" 3 0 1 = true := by decide
example : scanN "9300" 4 0 2 = true := by decide
example : scanN "93" 3 0 2 = false := by decide
example : segment_byte_at ["93", "00"] 0 = some 0x93 := by decide
example : segment_byte_at ["93", "00"] 1 = some 0x00 := by decide

end LinuxSem.Common.AsanHexScan
