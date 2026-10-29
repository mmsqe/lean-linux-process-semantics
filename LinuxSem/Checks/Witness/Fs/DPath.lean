/-
  * LinuxProcessSem.Checks.Witness.Fs.DPath — the getcwd (17) witness, and its proof

  Answers to Linux `fs/d_path.c`: this file holds the witnesses for the
  syscalls defined there, and no others.

  `Checks/Progress.lean` keeps the dispatcher and re-exports this module.
  A witness here exhibits one admissible outcome for a spec in the matching
  `Sys` module, which is what progress is proved from.

  The size band is `1 < size.toNat` — the UNSIGNED reading of the register,
  which is the band the kernel tests.  A witness answers with
  `Outcome SyscallEffect Model event`, and
  `ret_outcome (errno_ret ERANGE) m` is `Checks.Witness.Prelude`'s
  shorthand for "return `r`, change nothing, emit nothing".

  The guard occurs TWICE in a goal — once in `getcwd_spec`'s own `if`, once
  in the witness's — so the two branches are closed with
  `simp only [ite_eq_left h]` / `simp only [ite_eq_right h]`, which rewrites both
  occurrences, rather than with `rw`, which rewrites only the first.  That
  is the same note `Checks/Witness/Fs/EventFd.lean` carries.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.DPath

namespace LinuxSem.Checks.Witness.Fs.DPath

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.DPath
open LinuxSem.Checks.Witness.Prelude

/-- The witness takes -ERANGE rather than an injected errno: it is the
    answer the model actually derives from [size], while the other three
    are conditions no modeled state decides.  Above the band, failing
    closed is itself the admissible outcome. -/
def getcwd_witness (size : word) (m : Model) : Outcome SyscallEffect Model event :=
  if 1 < size.toNat then .unmodeled
  else ret_outcome (errno_ret ERANGE) m

theorem getcwd_witness_ok (size : word) (i : SyscallInput) (m : Model) :
    getcwd_spec size i m (getcwd_witness size m) := by
  generalize hP : (getcwd_spec size i m (getcwd_witness size m)) = Q at *
  by_cases hbig : 1 < size.toNat
  · rw [← hP]
    unfold getcwd_spec getcwd_witness
    simp only [ite_eq_left hbig]
    exact unmodeled_intro i m
  · rw [← hP]
    unfold getcwd_spec getcwd_witness
    simp only [ite_eq_right hbig]
    refine alt_r _ _ i m (.ok (mkEffect (errno_ret ERANGE) [] []) m []) ?_
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]

/-! ## Sanity checks (not library lemmas)

    There is no `vm_compute` goal in this module — it is one definition and
    one proof — so what follows checks the witness rather than proving
    library lemmas.  The checks pin the witness's two arms: inside
    the band it is the -ERANGE bare return, above it the decline.  The
    second is what makes the witness total, since `unmodeled` is itself
    an admissible outcome there.  `Outcome` has no `DecidableEq`, so each
    states its arm as an equation and closes it by unfolding the witness
    and discharging the guard by name. -/

/-- The model the checks run in: no fds, an empty VM ledger, an empty file
    system, EOF on stdin, no halt and no rlimit.  Nothing in it can
    matter to getcwd — the spec never looks at the model. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- `getcwd(NULL, 0)` is -ERANGE: the deterministic arm the kernel
    reaches after the whole path has been assembled and found not to
    fit. -/
example : getcwd_witness 0 demoModel = ret_outcome (errno_ret ERANGE) demoModel := by
  unfold getcwd_witness
  rw [ite_eq_right (by decide : ¬(1 < (0 : word).toNat))]

/-- …AND SO IS A ONE-BYTE BUFFER: one byte cannot hold even the
    terminating NUL. -/
example : getcwd_witness 1 demoModel = ret_outcome (errno_ret ERANGE) demoModel := by
  unfold getcwd_witness
  rw [ite_eq_right (by decide : ¬(1 < (1 : word).toNat))]

/-- ABOVE THE BAND THE WITNESS DECLINES, and `Unmodeled` is itself an
    admissible outcome there — which is what makes the witness total. -/
example : getcwd_witness 2 demoModel = .unmodeled := by
  unfold getcwd_witness
  rw [ite_eq_left (by decide : 1 < (2 : word).toNat)]

/-- A register at `2^64 - 1` reads as an enormous UNSIGNED size rather
    than as -1, so it is declined too. -/
example : getcwd_witness (BitVec.ofInt 64 (-1)) demoModel = .unmodeled := by
  unfold getcwd_witness
  rw [ite_eq_left (by decide : 1 < (BitVec.ofInt 64 (-1)).toNat)]

end LinuxSem.Checks.Witness.Fs.DPath
