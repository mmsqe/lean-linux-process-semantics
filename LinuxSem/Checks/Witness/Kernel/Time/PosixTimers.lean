/-
  * LinuxProcessSem.Checks.Witness.Kernel.Time.PosixTimers — the clock_gettime (113) witness, and its proof

  Answers to Linux [kernel/time/posix-timers.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r ws []` abbreviates `mkEffectU r ws [] [] [] []`,
  the clock is read as `((m_clock m).toNat : Int)`, and `Z_to_le_bytes` /
  `length_Z_to_le_bytes` are `BvBase`'s.

  Each proof peels the spec's reader with
  `refine bind_step inputSpec _ i m i m _ rfl ?_` — the reader is
  definitionally `.ok` — reduces with `try dsimp only`, and discharges a
  `choose` with `refine choose_ok _ _ i m ?_`.  A branch boolean is split
  with `cases`: the witness repeats every branch condition on the OUTCOME
  side of the goal, and `cases` substitutes the condition everywhere at
  once, whereas `rw [ite_eq_left …]` instantiates its pattern on the first copy
  only and leaves the other one standing.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers

namespace LinuxSem.Checks.Witness.Kernel.Time.PosixTimers

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxSem.Checks.Witness.Prelude

/-! ## The byte round trip (the inverse the witness consumes)

    [clock_gettime_bytes_ns] needs [bytes_le_to_Z]'s inverse: reading the
    little-endian bytes of a non-negative value back gives that value.
    `BvBase.bytes_le_to_Z_of_le_bytes` is the general statement, proved
    there from the `Nat` byte recursion, and
    `BvBase.bytes_le_to_Nat_Z_to_le_bytes` is the public `Nat` round trip it
    rests on.  What stays local, and `private`, is the same inverse at the
    shape the witness proof consumes. -/

/- The two facts `Z_to_le_bytes` needs — `((m : Int) >>> 8) = ((m / 256 : Nat) :
   Int)` and `(BitVec.ofInt 8 (m : Int)).toNat = m % 256` — are `BvBase`'s
   `int_shiftRight_8_natCast` and `toNat_ofInt_8_nat`, reached through the `open
   LinuxSem.LinuxProcessSem` above. -/

/-- The inverse of [Z_to_le_bytes] at a non-negative value: reading back
    the `8n` little-endian bytes of `z` returns `z`, provided `z` fits in
    them.  (The one instance of `BvBase.bytes_le_to_Z_of_le_bytes` this
    file uses, stated at the shape the witness proof consumes.) -/
private theorem bytes_le_to_Z_of_Z_to_le_bytes (n : Nat) (z : Int) (h0 : 0 ≤ z)
    (hlt : z < (2 : Int) ^ (8 * n)) :
    bytes_le_to_Z (Z_to_le_bytes n z) = z := by
  have hzn : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg h0
  conv => lhs; rw [show z = ((z.toNat : Nat) : Int) from hzn.symm]
  rw [bytes_le_to_Z, bytes_le_to_Nat_Z_to_le_bytes]
  have hlt' : z.toNat < 2 ^ (8 * n) := by
    rw [← Int.ofNat_lt, hzn]
    exact hlt
  rw [Nat.mod_eq_of_lt hlt', hzn]

/-! ## The witness -/

/-- The bytes of a `struct __kernel_timespec` recording `t` nanoseconds:
    the seconds and the normalized nanoseconds, each eight bytes
    little-endian — the split `ktime_to_timespec64` performs. -/
def clock_gettime_bytes (t : Int) : List byte :=
  Z_to_le_bytes 8 (t / 1000000000) ++ Z_to_le_bytes 8 (t % 1000000000)

/-- clock_gettime: the witness reads the clock WITHOUT ADVANCING IT.

    [timespec_ok_b] is satisfied non-strictly, so leaving the clock
    where it is is always admissible — which is what makes a witness
    possible at all for an arbitrary model state.  The bytes are the
    recorded nanosecond count split the way [ktime_to_timespec64]
    splits it, and [Z_to_le_bytes] is [bytes_le_to_Z]'s inverse
    ([BvBase.bytes_le_to_Z_of_le_bytes]), so the reading decodes back
    to exactly [m_clock m]. -/
def clock_gettime_witness (clkid tp : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if clockid_percall_b clkid then
    -- a per-call id reads 0 ns: [realtime_ok_b] relates a reading to
    -- nothing, so the smallest normalized timespec is always
    -- admissible and the witness needs no model state at all.
    match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => .unmodeled                            -- unwritable destination
    | some _ =>
        .ok (mkEffect (BitVec.ofInt 64 0) [(tp, clock_gettime_bytes 0)] [])
           m []
  else if ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) then
    -- CPU time reads 0 ns: [cputime_ok_b] holds the envelope on the
    -- SIGNED reading, and 0 is inside it in both directions, so the
    -- same smallest normalized timespec is admissible for the same
    -- reason, and again with no model state.
    match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => .unmodeled                            -- unwritable destination
    | some _ =>
        .ok (mkEffect (BitVec.ofInt 64 0) [(tp, clock_gettime_bytes 0)] [])
           m []
  else if !((clkid.toNat : Int) == CLOCK_MONOTONIC) then .unmodeled
  else if !decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)
  then .unmodeled
  else match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
       | none => .unmodeled                            -- unwritable destination
       | some _ =>
           let bs := clock_gettime_bytes ((m_clock m).toNat : Int)
           .ok (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [])
              (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m) []

/-- `clock_gettime_bytes`'s FIRST field decodes as the second count: the
    bytes `t / 10^9` are exactly `tv_sec`. -/
private theorem tv_sec_of_clock_gettime_bytes (t : Int) (h0 : 0 ≤ t)
    (hlt : t < (2 : Int) ^ 64) :
    tv_sec_of (clock_gettime_bytes t) = t / 1000000000 := by
  unfold tv_sec_of clock_gettime_bytes
  rw [List.take_append, length_Z_to_le_bytes, Nat.sub_self, List.take_zero,
    List.append_nil, List.take_of_length_le (by simp [length_Z_to_le_bytes])]
  exact bytes_le_to_Z_of_Z_to_le_bytes 8 (t / 1000000000)
    (Int.ediv_nonneg h0 (by decide)) (by
      have hle : t / 1000000000 ≤ t := Int.ediv_le_self 1000000000 h0
      rw [show 8 * 8 = 64 by decide]
      omega)

/-- ...and the SECOND field as the sub-second remainder. -/
private theorem tv_frac_of_clock_gettime_bytes (t : Int) :
    tv_frac_of (clock_gettime_bytes t) = t % 1000000000 := by
  unfold tv_frac_of clock_gettime_bytes
  rw [List.drop_append, length_Z_to_le_bytes, Nat.sub_self, List.drop_zero,
    List.drop_eq_nil_of_le (by simp [length_Z_to_le_bytes]), List.nil_append]
  exact bytes_le_to_Z_of_Z_to_le_bytes 8 (t % 1000000000)
    (Int.emod_nonneg t (by decide)) (by
      have h1 : t % 1000000000 < 1000000000 := Int.emod_lt_of_pos t (by decide)
      rw [show 8 * 8 = 64 by decide]
      omega)

/-- The witness's bytes decode to the recorded reading exactly. -/
theorem clock_gettime_bytes_ns (t : Int) (Ht : 0 ≤ t ∧ t < CLOCK_NS_ENVELOPE) :
    timespec_ns (clock_gettime_bytes t) = t
    ∧ tv_frac_of (clock_gettime_bytes t) = t % 1000000000
    ∧ (clock_gettime_bytes t).length = 16 := by
  obtain ⟨h0, hlt⟩ := Ht
  have hlt' : t < (2 : Int) ^ 64 := by
    have h2 : CLOCK_NS_ENVELOPE = (2 : Int) ^ 63 := rfl
    have h3 : (2 : Int) ^ 63 < (2 : Int) ^ 64 := by decide
    omega
  refine ⟨?_, tv_frac_of_clock_gettime_bytes t, ?_⟩
  · unfold timespec_ns
    rw [tv_sec_of_clock_gettime_bytes t h0 hlt', tv_frac_of_clock_gettime_bytes t]
    exact Int.ediv_mul_add_emod t 1000000000
  · unfold clock_gettime_bytes
    rw [List.length_append, length_Z_to_le_bytes, length_Z_to_le_bytes]

/-- A zero reading, as the SIGNED total [cputime_ok_b] reads: the two
    fields are `0` and `0`, so neither `s64` branch moves. -/
private theorem timespec_ns_signed_clock_gettime_bytes_zero :
    timespec_ns_signed (clock_gettime_bytes 0) = 0 := by
  have hsec : tv_sec_of (clock_gettime_bytes 0) = 0 := by
    simpa using tv_sec_of_clock_gettime_bytes 0 (by decide) (by decide)
  have hfrac : tv_frac_of (clock_gettime_bytes 0) = 0 := by
    simpa using tv_frac_of_clock_gettime_bytes 0
  unfold timespec_ns_signed
  rw [hsec, hfrac]
  simp

theorem clock_gettime_witness_ok (i : SyscallInput) (clkid tp : word) (m : Model) :
    clock_gettime_spec clkid tp i m (clock_gettime_witness clkid tp i m) := by
  unfold clock_gettime_spec clock_gettime_witness
  by_cases hrt : clockid_percall_b clkid = true
  · simp only [ite_eq_left hrt]
    refine bind_step inputSpec _ i m i m _ rfl ?_
    try dsimp only
    cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => exact unmodeled_intro _ _
    | some bs0 =>
      obtain ⟨hns0, hfrac0, hlen0⟩ :=
        clock_gettime_bytes_ns 0 ⟨by decide, by decide⟩
      refine bind_step (choose (fun bs => realtime_ok_b bs = true)) _
        i m (clock_gettime_bytes 0) m _ ?_ ?_
      · refine choose_ok _ _ i m ?_
        simp only [realtime_ok_b, hlen0, hns0, hfrac0]
        decide
      · exact pure_ok _ i m
  · simp only [ite_eq_right hrt]
    by_cases hcp : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
    · simp only [ite_eq_left hcp]
      refine bind_step inputSpec _ i m i m _ rfl ?_
      try dsimp only
      cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
      | none => exact unmodeled_intro _ _
      | some bs0 =>
        obtain ⟨hns0, hfrac0, hlen0⟩ :=
          clock_gettime_bytes_ns 0 ⟨by decide, by decide⟩
        refine bind_step (choose (fun bs => cputime_ok_b bs = true)) _
          i m (clock_gettime_bytes 0) m _ ?_ ?_
        · refine choose_ok _ _ i m ?_
          simp only [cputime_ok_b, hlen0, hfrac0,
            timespec_ns_signed_clock_gettime_bytes_zero]
          decide
        · exact pure_ok _ i m
    · simp only [ite_eq_right hcp]
      by_cases hid : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
      · simp only [ite_eq_left hid]
        exact unmodeled_intro _ _
      · simp only [ite_eq_right hid]
        cases henv : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) with
        | false =>
          -- the recorded clock is outside the envelope: the arm declines
          refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
          simpa [henv] using unmodeled_intro (A := SyscallEffect) i m
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          have hlt : ((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE := by
            rw [decide_eq_true_eq] at henv
            exact henv
          obtain ⟨hns, hfrac, hlen⟩ := clock_gettime_bytes_ns ((m_clock m).toNat : Int)
            ⟨Int.natCast_nonneg _, hlt⟩
          have h1 : ((m_clock m).toNat : Int) % 1000000000 < 1000000000 :=
            Int.emod_lt_of_pos _ (by decide)
          have h2 : ((m_clock m).toNat : Int) ≤ ((m_clock m).toNat : Int) :=
            Int.le_refl _
          refine bind_step getModelSpec _ i m m m _ rfl ?_
          try dsimp only
          simp only [henv, Bool.not_true, Bool.false_eq_true, ite_false]
          refine bind_step inputSpec _ i m i m _ rfl ?_
          try dsimp only
          cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
          | none => exact unmodeled_intro _ _
          | some bs0 =>
            have hok : timespec_ok_b (clock_gettime_bytes ((m_clock m).toNat : Int))
                (m_clock m) = true := by
              simp only [timespec_ok_b, hlen, hns, hfrac, h1, h2, hlt]
              decide
            refine bind_step (choose (fun bs => timespec_ok_b bs (m_clock m) = true)) _
              i m (clock_gettime_bytes ((m_clock m).toNat : Int)) m _ ?_ ?_
            · exact choose_ok _ _ i m hok
            · refine bind_step (modify (with_clock
                  (BitVec.ofInt 64 (timespec_ns (clock_gettime_bytes
                    ((m_clock m).toNat : Int))))))
                _ i m ()
                (with_clock (BitVec.ofInt 64 (timespec_ns (clock_gettime_bytes
                  ((m_clock m).toNat : Int)))) m) _ ?_ ?_
              · exact modify_ok _ i m
              · exact pure_ok _ _ _

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal (the `Cases/` tree is
    where its properties are pinned), so these are the module's own checks
    in the style of AGENTS.md's "definition of done": they pin the one
    computable definition here — `ktime_to_timespec64`'s split — on literal
    byte lists. -/

/-- A zero reading is sixteen zero bytes: both fields are `0`. -/
example : clock_gettime_bytes 0 = List.replicate 16 0 := by decide

/-- One second and two nanoseconds: `tv_sec = 1`, `tv_nsec = 2`, each
    little-endian. -/
example : clock_gettime_bytes 1000000002 = Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 2 := by
  decide

/-- The sub-second field carries no whole second out: 1.5 s splits as
    `tv_sec = 1`, `tv_nsec = 500000000`. -/
example : clock_gettime_bytes 1500000000
    = Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 500000000 := by decide

/-- A `struct __kernel_timespec` is exactly 16 bytes, for any reading. -/
example : (clock_gettime_bytes 123456789).length = 16 := by decide

end LinuxSem.Checks.Witness.Kernel.Time.PosixTimers




