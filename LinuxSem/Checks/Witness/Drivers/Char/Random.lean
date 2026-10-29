/-
  * LinuxProcessSem.Checks.Witness.Drivers.Char.Random — the getrandom (278) witnesses, and their proofs

  Answers to Linux [drivers/char/random.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r ws []` abbreviates
  `mkEffectU r ws [] [] [] []`, and `ret_outcome` is
  `Checks.Witness.Prelude`'s "return `r`, change nothing, emit nothing".

  The zero byte list is `List.replicate buflen.toNat (BitVec.ofInt 8 0)` —
  the word's own `Nat` value is the count, one byte per requested byte — so
  its length is `List.length_replicate` and no truncation lemma is
  needed.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random

namespace LinuxSem.Checks.Witness.Drivers.Char.Random

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi (GRND_NONBLOCK GRND_RANDOM)
open LinuxSem.LinuxProcessSem.Sys.Uaccess (rw_bytes_max modeled_rw_count)
open LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random
  (getrandom_errnos getrandom_small_max getrandom_spec)
open LinuxSem.Checks.Witness.Prelude

/-- getrandom's witness.  A nonzero request of at most
    [Random.getrandom_small_max] bytes has ONE admissible shape — full
    delivery — so the witness exhibits it with all-zero bytes (the
    bytes are the environment's; any list of the right length is
    admissible).  Every other request answers -EINTR, which joins every
    range verdict of the zero-byte arm and the delivery alternative of
    a large request. -/
def getrandom_witness (buf buflen flags : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK))
  then .unmodeled
  else if !modeled_rw_count buflen then .unmodeled   -- see [rw_bytes_max]
  else match read_bytes_map i.in_wmem buf buflen with
       | none => .unmodeled                          -- unwritable destination
       | some _ =>
           if !w_is0 buflen && decide ((buflen.toNat : Int) ≤ getrandom_small_max)
           then -- the small request: delivered in full, and only that
             let bs := List.replicate buflen.toNat (BitVec.ofInt 8 0)
             .ok (mkEffect (len_word bs) [(buf, bs)] []) m []
           else ret_outcome (errno_ret EINTR) m   -- -EINTR joins every other verdict

/-- EINTR is the one errno the interrupted alternative can return, so this
    is the shape it contributes to the witness (see
    [Checks.Witness.Prelude.errno_from_witness]). -/
private theorem getrandom_interrupted_witness (i : SyscallInput) (m : Model) :
    bind (errno_from getrandom_errnos) (fun e => err_ret e) i m
      (.ok (mkEffect (errno_ret EINTR) [] []) m []) :=
  bind_step (errno_from getrandom_errnos) (fun e => err_ret e) i m EINTR m _
    (errno_from_witness getrandom_errnos EINTR i m (by decide))
    (pure_ok (mkEffect (errno_ret EINTR) [] []) i m)

/-- The witness inhabits the spec: each of its arms is one the spec
    admits.  The two gates and the destination read are the spec's own;
    past them the zero-byte arm's verdict only picks WHICH zero answer the
    spec offers, -EINTR joining either; the small-request arm is the spec's
    full delivery of a right-length byte list; and the large-request arm is
    the interrupted alternative.

    The proof is a `by_cases` on the shared boolean SUBTERM
    (`!w_is0 buflen`, `decide …`) followed by a `simp only [ite_eq_left …]` /
    `simp only [ite_eq_right …]`: the goal carries the DECISION TWICE — once as
    the spec's `if` and once as the witness's — and their branches have
    different types (`Sys` vs `outcome`), so a plain `rw [ite_eq_left h]` would
    instantiate the branch metavariables from the first occurrence and miss
    the second.  A simp
    rule built from `ite_eq_left h` / `ite_eq_right h` is matched afresh at every
    occurrence, which reduces both; the witness's own condition is the
    conjunction `!w_is0 buflen && decide …`, so its equation (`hwit`) is
    proved separately and fed to `ite_eq_left`/`ite_eq_right` the same way. -/
theorem getrandom_witness_ok (buf buflen flags : word) (i : SyscallInput)
    (m : Model) :
    getrandom_spec buf buflen flags i m
      (getrandom_witness buf buflen flags i m) := by
  unfold getrandom_spec getrandom_witness
  by_cases hf : (!(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK))) = true
  · -- unmodeled flags: both sides fail closed
    simp only [ite_eq_left hf]
    exact unmodeled_intro (A := SyscallEffect) i m
  · simp only [ite_eq_right hf]
    by_cases hn : (!modeled_rw_count buflen) = true
    · -- over the transfer bound: both sides fail closed
      simp only [ite_eq_left hn]
      exact unmodeled_intro (A := SyscallEffect) i m
    · simp only [ite_eq_right hn]
      refine bind_step inputSpec _ i m i m _ rfl ?_
      try dsimp only
      cases hw : read_bytes_map i.in_wmem buf buflen with
      | none =>
        try dsimp only
        exact unmodeled_intro (A := SyscallEffect) i m
      | some w =>
        try dsimp only
        by_cases hnb : (!w_is0 buflen) = true
        · -- a nonzero request
          simp only [ite_eq_left hnb]
          by_cases hsm : decide ((buflen.toNat : Int) ≤ getrandom_small_max) = true
          · -- the small request: the chosen list has exactly [buflen] bytes
            have hwit : (!w_is0 buflen &&
                decide ((buflen.toNat : Int) ≤ getrandom_small_max)) = true := by
              simp [hnb, hsm]
            simp only [ite_eq_left hwit, ite_eq_left hsm]
            refine bind_step (choose (fun bs : List byte =>
                (bs.length : Int) = (buflen.toNat : Int)))
              (fun bs => pure (mkEffect (len_word bs) [(buf, bs)] [])) i m
              (List.replicate buflen.toNat (BitVec.ofInt 8 0)) m _ ?_ ?_
            · exact choose_ok _ _ i m (by simp [List.length_replicate])
            · exact pure_ok _ _ _
          · -- the large request: -EINTR joins the delivery alternative
            have hwit : ¬((!w_is0 buflen &&
                decide ((buflen.toNat : Int) ≤ getrandom_small_max)) = true) := by
              simp [hnb, hsm]
            simp only [ite_eq_right hwit, ite_eq_right hsm]
            exact alt_l _ _ _ _ _ (getrandom_interrupted_witness i m)
        · -- the zero-byte arm: -EINTR joins every range verdict
          have hwit : ¬((!w_is0 buflen &&
              decide ((buflen.toNat : Int) ≤ getrandom_small_max)) = true) := by
            simp [hnb]
          simp only [ite_eq_right hwit, ite_eq_right hnb]
          by_cases ha : access_okb buf (buflen.toNat : Int) = true
          · simp only [ite_eq_left ha]
            exact alt_l _ _ _ _ _ (getrandom_interrupted_witness i m)
          · simp only [ite_eq_right ha]
            exact alt_l _ _ _ _ _ (getrandom_interrupted_witness i m)

/-! readlinkat witness: [Unmodeled] on an unmodeled dirfd (fail closed, but
    never stuck), otherwise the deterministic -EINVAL return. -/

/- =========================================================================
   exit (93) / exit_group (94) — deterministic
   ========================================================================= -/

end LinuxSem.Checks.Witness.Drivers.Char.Random
