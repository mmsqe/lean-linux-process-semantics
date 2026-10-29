/-
  * LinuxSem.Checks.Cases.Fs.Ioctl — worked examples over ioctl (29)

  Worked cases over `Sys.Fs.Ioctl`, which answers to Linux [fs/ioctl.c]:
  the examples for the syscalls defined there, and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have are supplied as local transparent `abbrev`s below,
  DEFINITIONALLY EQUAL to what they stand for, so every statement below
  denotes exactly the same claim:
  - `bv_unsigned w` is `(w.toNat : Int)` and `Z_to_bv n z` is
    `BitVec.ofInt n z`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`;
  - `nth_error l n` is `l[n]?` and `existsb p l` is `l.any p`;
  - `bv_leu`/`bv_ltu` come from `Riscv.Prelude`, reached through
    `open LinuxSem.Riscv`, so they need no shim;
  - a record field is read by dot notation here (`e.eff_writes`), the
    same projection the prelude applies as a function;
    `m_fds`/`m_fs`/`m_stdin`/`m_pipes` are already functions
    (`StateLedger`), so they need no shim;
  - constructors of an inductive live in the type's namespace, so the
    bare `FdChannel`/`FdFile`/… are `FdEntry.FdChannel`/… and `SkFresh`
    is `SockState.SkFresh`.  `mkInput` is `SyscallInput.mkInput`;
    `mkEffect`/`mkModel`/`mkVmMaps`/`errno_ret` are plain definitions
    and keep their bare names.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  `decide` cannot be the rule: `check_result` carries
  a `Model` and so has no `DecidableEq`.

  Imports.  `Checks.Cases.Prelude` (and, where it is needed,
  `Checks.Cases.Fs.ReadWrite`) is imported directly; the re-export for
  the tree above this file is left to the root module.

  `Forall`.  Two of the examples quantify over a concrete request list.
  Lean 4.31's core library has no `List.Forall`, so `Forall` is supplied
  as the transparent `abbrev` below — `∀ x ∈ l, p x`, the same predicate
  the rest of the tree uses for that constant — and the statements read
  as written.  Each proof is the membership intro followed by `rfl` at
  each element; the element list is untouched.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.Ioctl
import LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Syscall

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
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.Ioctl
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Ioctl

/-! ## The prelude's abbreviations, restored

    Each of these is a transparent alias, so it
    changes no statement's meaning. -/

/-- `bv_unsigned` (`BvBase`): the unsigned value of a bitvector, in
    `Int` so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `bv_signed`: the signed value of a bitvector, as an `Int`. -/
abbrev bv_signed {n : Nat} (w : BitVec n) : Int := w.toInt

/-- `Z_to_bv`: an `Int` re-wrapped at width `n`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `Z.eqb` (and `Nat.eqb`), over any `BEq`. -/
abbrev zeqb {α : Type} [BEq α] (a b : α) : Bool := a == b

/-- `Z.leb` on `Int`. -/
abbrev zleb (a b : Int) : Bool := decide (a ≤ b)

/-- `Z.ltb` on `Int`. -/
abbrev zltb (a b : Int) : Bool := decide (a < b)

/-- `nth_error`: `Option`-returning list indexing. -/
abbrev nth_error {α : Type} [Inhabited α] (l : List α) (n : Nat) : Option α := l[n]?

/-- `in_mem` as a function (a `SyscallInput` field projection). -/
abbrev in_mem (i : SyscallInput) : word → Option byte := i.in_mem
/-- `in_wmem` as a function. -/
abbrev in_wmem (i : SyscallInput) : word → Option byte := i.in_wmem
/-- `eff_ret` as a function. -/
abbrev eff_ret (e : SyscallEffect) : word := e.eff_ret
/-- `eff_writes` as a function. -/
abbrev eff_writes (e : SyscallEffect) : List (word × List byte) := e.eff_writes
/-- `eff_zeros` as a function. -/
abbrev eff_zeros (e : SyscallEffect) : List (word × word) := e.eff_zeros
/-- `eff_unmaps` as a function. -/
abbrev eff_unmaps (e : SyscallEffect) : List (word × word) := e.eff_unmaps
/-- `eff_copies` as a function. -/
abbrev eff_copies (e : SyscallEffect) : List MemCopy := e.eff_copies
/-- `eff_copyins` as a function. -/
abbrev eff_copyins (e : SyscallEffect) : List (word × Nat) := e.eff_copyins

/-- `Forall p l` — `∀ x ∈ l, p x`, the elementwise conjunction the rest
    of the tree uses for this constant.  Lean 4.31's core library has no
    `List.Forall` inductive, so on a concrete list literal this is the
    same conjunction with `p` at each element. -/
abbrev Forall {α : Type} (p : α → Prop) (l : List α) : Prop := ∀ x ∈ l, p x

/-! * LinuxSem.Checks.Cases.Fs.Ioctl — worked examples over ioctl (29)

    Worked cases over `Sys.Fs.Ioctl`, which answers to Linux [fs/ioctl.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/

theorem ioctl_tiocgwinsz_enotty :
  check_syscall (SyscallInput.mkInput 29 [1, TIOCGWINSZ, 4096, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
:= by rfl

theorem ioctl_tty_only_requests_all_enotty :
  Forall (fun req =>
    check_syscall (SyscallInput.mkInput 29 [1, req, 4096, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
    = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [])
    [TCGETS, TCSETS, TIOCSCTTY, TIOCGWINSZ,
     TIOCSWINSZ, TIOCNOTTY, TIOCGPTN, TIOCSPTLCK]
:= by
  intro req hreq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreq
  rcases hreq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ioctl_other_request_is_error :
  Forall (fun req =>
    check_syscall (SyscallInput.mkInput 29 [1, req, 4096, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
    = check_result.CheckUnmodeled)
    [Z_to_bv 64 21531, Z_to_bv 64 21537]    /- FIONREAD 0x541B, FIONBIO 0x5421 -/
:= by
  intro req hreq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreq
  rcases hreq with rfl | rfl <;> rfl

/- -------------------------------------------------------------------------
   THE NULL DEVICE

   [State.FdDevNull] is the descriptor [openat_devnull_spec] mints, and
   the reason this kind needs its own examples is that the two above run
   on fd 1, which [init_model] makes an [FdChannel] -- a different
   constructor, so nothing they prove reaches this arm.

   The model below keeps the three standard descriptors and adds the
   null device on 3, which is the shape a program that [fopen]s
   "/dev/null" for writing is in: musl's [__fdopen] issues TIOCGWINSZ on
   the fresh stream to pick a buffering mode, and that is the call these
   examples are about.
   ------------------------------------------------------------------------- -/

def ioctl_devnull_model : Model :=
  with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)))
              3 (FdEntry.FdDevNull false true))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))

theorem ioctl_devnull_tiocgwinsz_enotty :
  check_syscall (SyscallInput.mkInput 29 [3, TIOCGWINSZ, 4096, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOTTY) [] []) ioctl_devnull_model
  = check_result.CheckOk ioctl_devnull_model []
:= by rfl

theorem ioctl_devnull_tty_only_requests_all_enotty :
  Forall (fun req =>
    check_syscall (SyscallInput.mkInput 29 [3, req, 4096, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret ENOTTY) [] []) ioctl_devnull_model
    = check_result.CheckOk ioctl_devnull_model [])
    [TCGETS, TCSETS, TIOCSCTTY, TIOCGWINSZ,
     TIOCSWINSZ, TIOCNOTTY, TIOCGPTN, TIOCSPTLCK]
:= by
  intro req hreq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreq
  rcases hreq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! FAIL-CLOSED beside the conforming answer: a request outside the
    eight is still declined ON THIS KIND, so the arm answers the eight
    rather than answering the descriptor.  The two here are the ones
    [do_vfs_ioctl] claims before the device is ever reached -- FIONBIO
    really succeeds and sets O_NONBLOCK, which this model does not
    carry, and FIONREAD on a character device is handed back to
    [vfs_ioctl] and so is -ENOTTY, an answer the model could give but
    has not written down.  Either way the model stops. -/
theorem ioctl_devnull_other_request_is_unmodeled :
  Forall (fun req =>
    check_syscall (SyscallInput.mkInput 29 [3, req, 4096, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect 0 [] []) ioctl_devnull_model
    = check_result.CheckUnmodeled)
    [Z_to_bv 64 21537, Z_to_bv 64 21531]    /- FIONBIO 0x5421, FIONREAD 0x541B -/
:= by
  intro req hreq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreq
  rcases hreq with rfl | rfl <;> rfl

end LinuxSem.Checks.Cases.Fs.Ioctl
