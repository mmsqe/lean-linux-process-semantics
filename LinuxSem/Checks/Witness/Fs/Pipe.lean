/-
  * LinuxSem.Checks.Witness.Fs.Pipe — the pipe2 (59) witness, and its proof

  Answers to Linux [fs/pipe.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  pipe2 allocates, so — as `dup`'s witness does — the witness takes an
  environment-failure branch on every arm that could install descriptors:
  `-EMFILE`, the head of `Sys.Fs.Pipe.pipe2_errnos`, which the spec offers
  on all three of its nondeterministic arms (an unwritable destination, a
  fully writable one, and an unwritable destination with a writable
  prefix).  Nothing is installed and the model is untouched, which is what
  makes the witness admissible whatever the fd table holds.

  `Checks.Witness.Prelude` supplies every helper this arm uses
  ([ret_outcome], [bind_step], [errno_head_witness]); no other witness
  module is imported here.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r [] []` abbreviates
  `mkEffectU r [] [] [] [] []` (`State.lean`).

  The spec is opened with two `bind_step`s, and each scrutinee is then
  split with `by_cases` / `cases`: the equation rewrites BOTH sides at
  once, because the spec and the witness share every test term, and the
  reduction that follows is the `dsimp only` of the `srw` macro.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Pipe

namespace LinuxSem.Checks.Witness.Fs.Pipe

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Pipe
open LinuxSem.Checks.Witness.Prelude

/-- pipe2's witness: -EINVAL for a flag word outside the accepted mask
    (raised before anything else), the fail-closed [Unmodeled] for the
    three arms the model declines, and `-EMFILE` everywhere the spec is
    nondeterministic — the read and write descriptors are the kernel's
    choice, so the witness never names them.

    The three `-EMFILE` arms are the spec's three `alt`es: an
    `access_ok`-refused destination, a wholly writable one, and one whose
    first byte is writable but whose tail is not. -/
def pipe2_witness (fildes flags : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)
  then ret_outcome (errno_ret EINVAL) m
  else if !(w_is0 flags) then .unmodeled
  else
  match pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
  | some _ => .unmodeled
  | none =>
      if !(access_okb fildes 8) then ret_outcome (errno_ret EMFILE) m
      else
      match read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
      | some _ => ret_outcome (errno_ret EMFILE) m
      | none =>
          match read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
          | none => ret_outcome (errno_ret EMFILE) m
          | some _ => .unmodeled

theorem pipe2_witness_ok (fildes flags : word) (i : SyscallInput) (m : Model) :
    pipe2_spec fildes flags i m (pipe2_witness fildes flags i m) := by
  unfold pipe2_spec pipe2_witness
  refine bind_step inputSpec _ i m i m _ rfl ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  -- every scrutinee here is closed over the quantified variables, so each
  -- equation below rewrites the spec and the witness at once
  by_cases hbad : (!(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)) = true
  · simp only [ite_eq_left hbad, err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  · by_cases hnz : (!(w_is0 flags)) = true
    · simp only [ite_eq_right hbad, ite_eq_left hnz, unmodeled, ret_outcome]
    · cases hid : pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
      | some st =>
        simp only [ite_eq_right hbad, ite_eq_right hnz, unmodeled]
      | none =>
        by_cases hak : (!(access_okb fildes 8)) = true
        · -- [access_ok] refuses the range: the spec offers the injected
          -- errno beside -EFAULT, and the witness takes the injected head
          simp only [ite_eq_right hbad, ite_eq_right hnz, ite_eq_left hak]
          refine alt_l _ _ i m _ ?_
          refine bind_step (errno_from pipe2_errnos) (fun e => err_ret e) i m EMFILE m _ ?_ ?_
          · exact errno_from_witness pipe2_errnos EMFILE i m (by simp [pipe2_errnos])
          · simp only [err_ret, ret_only, ret_outcome, mkEffect,
              LinuxSem.LinuxProcessSem.pure]
        · cases h8 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
          | some w8 =>
            -- the whole destination is writable: the injectable errno is
            -- the witness, since it is admissible whatever the fd table
            -- holds
            simp only [ite_eq_right hbad, ite_eq_right hnz, ite_eq_right hak]
            refine alt_l _ _ i m _ ?_
            refine bind_step (errno_from pipe2_errnos) (fun e => err_ret e) i m EMFILE m
              _ ?_ ?_
            · exact errno_from_witness pipe2_errnos EMFILE i m (by simp [pipe2_errnos])
            · simp only [err_ret, ret_only, ret_outcome, mkEffect,
                LinuxSem.LinuxProcessSem.pure]
          | none =>
            cases h1 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
            | some w1 =>
              -- a writable prefix and an unwritable tail: fail closed
              simp only [ite_eq_right hbad, ite_eq_right hnz, ite_eq_right hak, unmodeled]
            | none =>
              simp only [ite_eq_right hbad, ite_eq_right hnz, ite_eq_right hak]
              refine alt_l _ _ i m _ ?_
              refine bind_step (errno_from pipe2_errnos) (fun e => err_ret e) i m EMFILE m
                _ ?_ ?_
              · exact errno_from_witness pipe2_errnos EMFILE i m (by simp [pipe2_errnos])
              · simp only [err_ret, ret_only, ret_outcome, mkEffect,
                  LinuxSem.LinuxProcessSem.pure]

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal either.  These pin each
   arm of the witness — -EINVAL for bad flags, [Unmodeled] for an accepted
   but uninterpreted flag, the injected -EMFILE on a fully writable
   destination, and the fail-closed decline for a partially writable one —
   which is the claim the proof above follows. -/

/-- Every address is writable, every byte zero. -/
private def portWmem : word → Option byte := fun _ => some 0

/-- The model the checks run in: an empty fd table, an empty pipe table, an
    empty VM ledger, EOF on stdin and no halt. -/
private def portModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- A `pipe2` input: `fildes = 0x1000`, `flags = 0`. -/
private def portInput : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := portWmem }

/-- A bit outside the accepted mask is -EINVAL, before the fd table, the
    pipe table or the destination is looked at. -/
example :
    pipe2_witness 0x1000 1 portInput portModel
      = ret_outcome (errno_ret EINVAL) portModel := by
  have hbad : (!(z_ldiff ((1 : word).toNat : Int) pipe2_flags_mask == 0)) = true := by
    decide
  simp only [pipe2_witness]
  rw [ite_eq_left hbad]

/-- An accepted but uninterpreted flag (`O_CLOEXEC`) declines. -/
example :
    pipe2_witness 0x1000 0x80000 portInput portModel = .unmodeled := by
  have hbad : (!(z_ldiff ((0x80000 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hnz : (!(w_is0 (0x80000 : word))) = true := by decide
  simp only [pipe2_witness]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_left hnz]

/-- The model's fd and pipe tables are both empty in the fixture: no pipe id
    is taken, so the witness reaches the destination tests. -/
example : pipe_lookup (m_pipes portModel) (pipe_new_id (m_pipes portModel)) = none := by
  decide

/-- With the whole destination writable the witness takes the injected
    `-EMFILE` — the descriptor numbers are the kernel's, never the
    witness's. -/
example :
    pipe2_witness 0x1000 0 portInput portModel
      = ret_outcome (errno_ret EMFILE) portModel := by
  have hbad : (!(z_ldiff ((0 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hz : (!(w_is0 (0 : word))) = false := by decide
  have hak : (!(access_okb (0x1000 : word) 8)) = false := by decide
  have h8 : read_bytes_map portWmem (0x1000 : word) (BitVec.ofInt 64 8)
      = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  simp only [pipe2_witness, portInput]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_right (by rw [hz]; simp)]
  simp only [portModel, mkModel, m_pipes, pipe_new_id, pipe_lookup]
  rw [ite_eq_right (by rw [hak]; simp)]
  simp only [h8]

/-- A writable prefix with an unwritable tail declines: `copy_to_user`
    leaves an architecture-dependent number of bytes behind. -/
private def oneByteWmem : word → Option byte :=
  fun a => if a == (0x1000 : word) then some 0 else none

private def portInputPartial : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := oneByteWmem }

example : pipe2_witness 0x1000 0 portInputPartial portModel = .unmodeled := by
  have hbad : (!(z_ldiff ((0 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hz : (!(w_is0 (0 : word))) = false := by decide
  have hak : (!(access_okb (0x1000 : word) 8)) = false := by decide
  have h8 : read_bytes_map oneByteWmem (0x1000 : word) (BitVec.ofInt 64 8) = none := by
    decide
  have h1 : read_bytes_map oneByteWmem (0x1000 : word) (BitVec.ofInt 64 1) = some [0] := by
    decide
  simp only [pipe2_witness, portInputPartial]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_right (by rw [hz]; simp)]
  simp only [portModel, mkModel, m_pipes, pipe_new_id, pipe_lookup]
  rw [ite_eq_right (by rw [hak]; simp)]
  simp only [h8, h1]

end LinuxSem.Checks.Witness.Fs.Pipe
