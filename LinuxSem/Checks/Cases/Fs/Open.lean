/-
  * LinuxSem.Checks.Cases.Fs.Open — worked examples over openat (56), close (57), ftruncate (46), faccessat (48), faccessat2 (439)

  Worked cases over `Sys.Fs.Open`, which answers to Linux [fs/open.c]:
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
  - `nth_error l n` is `l[n]?`, `existsb p l` is `l.any p` (`List.any`,
    the name used throughout this file), `repeat x n` is
    `List.replicate n x` (argument order swapped), `Z.lor a b` is
    `zlor a b`, `fst`/`snd` are `Prod.fst`/`Prod.snd`, `~ In b l` is
    `b ∉ l`;
  - a record field is read by dot notation here (`e.eff_writes`), the
    same projection the prelude applies as a function;
    `m_fds`/`m_fs`/`m_stdin`/`m_pipes` are already functions
    (`StateLedger`), so they need no shim.

  Renamed locals: `open` and `have`.  Lean has no local variable that
  may be called `open` or `have` (both are keywords), so the two
  `let`-bound helpers named `open` and `have` elsewhere are spelled
  `opn` and `hfs` here.  Nothing else about those statements changes —
  the equations are the same equations.

  The dropped proof device.  One proof device, `key_byte_neq`, is used
  only inside `relative_key_inputs_are_valid`.  It has no declaration
  counterpart in Lean and no statement to carry over, so it is not
  reproduced: the step it performed is the
  `show (n : byte) ≠ path_slash_byte` + `decide` pair in that proof.

  Imports.  `Checks.Cases.Prelude` and `Checks.Cases.Fs.ReadWrite` are
  both imported directly; the re-export for the tree above this file is
  left to the root module.  One name comes from
  `Checks.Cases.Fs.ReadWrite` — `mem_open_write` — and is re-stated as a
  local `abbrev` below rather than by opening that namespace, so that
  the two files' `bv_unsigned`-style shims cannot shadow one another.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  `decide` cannot be the rule: `check_result` carries
  a `Model` and so has no `DecidableEq`.

  The QUANTIFIED lemmas, one per row:
  - `not_in_bytes_of_existsb` — induction-free: `List.any_eq_true` on
    the membership hypothesis contradicts the `= false` premise;
  - `device_key_images_are_not_relative` — the `Forall_inv` step
    becomes specialising the `∀ pf ∈ …` at the singleton;
  - `device_key_inputs_are_not_valid` — `valid_input` is split into its
    eleven clauses and the keys one is handed to the lemma above;
  - `relative_key_inputs_are_valid` — the structural hammer
    `repeat split; … repeat first [ … ]`, done clause by clause
    (eleven per input, three inputs);
  - `urandom_stream_runs_out` — the three closed calls by `rfl`, the
    fourth by `stream_take_z_infinite_length`;
  - `urandom_same_bytes_in_general` — `check_read_urandom_same_stream`.

  One deviation.  Two `let`-bound file-system literals (`sibling`,
  `exact`) carry an explicit `: Fs.Fs` because Lean's numeral
  defaulting would otherwise fix their element type at `Nat` before the
  use site is seen.  The value is the one inference selects.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.ReadWrite
import LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.Common.RocqSpelling

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
open LinuxSem.LinuxProcessSem.Sys.Fs.Open
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Open

open LinuxSem.Common.RocqSpelling

/-! The Rocq spellings used below (`bv_unsigned`, `Z_to_bv`, …) are the shared transparent aliases of `LinuxSem.Common.RocqSpelling`. -/

/-- `Checks.Cases.Fs.ReadWrite`'s `mem_open_write`, spelled through its
    own namespace so that opening this one does not drag the other's shims
    in. -/
abbrev mem_open_write : word → Option byte :=
  LinuxSem.Checks.Cases.Fs.ReadWrite.mem_open_write

/-- `Z.lor` on the non-negative arguments this file uses. -/
abbrev zlor (a b : Int) : Int := Int.ofNat (a.toNat ||| b.toNat)

/-! * LinuxProcessSem.Checks.Cases.Fs.Open — worked examples over openat (56), close (57), ftruncate (46), faccessat (48), faccessat2 (439)

    Worked cases over `Sys.Fs.Open`, which answers to Linux [fs/open.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/


theorem openat_live_dirfd_still_unmodeled :
  check_syscall
    (SyscallInput.mkInput 56 [1, 8192, 0, 0, 0, 0]
       (fun a => if bv_eqb a 8192 then some 102
                 else if bv_eqb a 8193 then some 0 else none)
       (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckUnmodeled
:= by rfl

/-! Bit 31 is part of every one of these 32-bit arguments, and nothing
    else pins it: each truncation test uses a high half of the form
    2^32·k, which a WRONG truncation keeping only the low 31 bits would
    pass.  A whence of 2^31 + SEEK_END names no origin (-EINVAL from
    [ksys_lseek]'s [whence <= SEEK_MAX] test, fs/read_write.c,
    v6.18.46), an fd of 2^31 + 1 is not stdout, and a request of
    2^31 + TIOCGWINSZ is not TIOCGWINSZ. -/

theorem openat_empty_path_enoent :
  check_syscall
    (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 0, 0, 0]
       (fun a => if bv_eqb a 8192 then some 0 else none)
       (fun _ => none))
    (with_copyins [(8192, 1)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([], [104])] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [([], [104])] IEof)) []
:= by rfl

/-! O_NONBLOCK is an IGNORED bit, on every modeled shape: the open lands
    in exactly the model the same open without it lands in.  Only a
    literal can say that, because it is an EQUALITY BETWEEN TWO FLAG
    WORDS — a real run issues one word, so it can show the
    O_NONBLOCK open succeeds but never that the two agree.  Two images
    are needed to keep every equation between two SUCCESSES: "f" is
    present for the read and clobber shapes, absent for the exclusive
    ones, which refuse an existing path.

    The second half pins the boundary the first half must not have
    dragged along.  O_RDWR is an ADMITTED access mode, so it joins
    the first half as a fifth ignored-bit equation and a fifth success;
    what stays [CheckUnmodeled] beside it is O_NOCTTY, meaningful only
    on a terminal the model does not have, and the O_RDWR spellings
    whose arms do not exist — O_RDWR|O_APPEND, O_RDWR|O_EXCL without
    O_CREAT, and O_RDWR|O_DIRECTORY ([Fs.Open.modeled_open_flags] says
    why each). -/
theorem o_nonblock_is_an_ignored_open_flag :
  let opn fs fl := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           mem_open_write (fun _ => none))
        (with_copyins [(8192, 2)] (mkEffect 3 [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let ok r := (match r with | check_result.CheckOk _ _ => true | _ => false ) ;
  let hfs : Fs.Fs := [([102], [104, 105])] ;
  let absent := [] ;
  opn hfs (0 + O_NONBLOCK) = opn hfs 0
  ∧ opn hfs (wr_create_flags + O_NONBLOCK) = opn hfs wr_create_flags
  ∧ opn absent (excl_create_flags + O_NONBLOCK)
     = opn absent excl_create_flags
  ∧ opn absent (excl_create_flags + O_TRUNC + O_NONBLOCK)
     = opn absent (excl_create_flags + O_TRUNC)
  ∧ opn hfs (O_RDWR + O_NONBLOCK) = opn hfs O_RDWR
  /- every one of those five is a SUCCESS at fd 3, not two matching refusals -/
  ∧ ok (opn hfs (0 + O_NONBLOCK)) = true
  ∧ ok (opn hfs (wr_create_flags + O_NONBLOCK)) = true
  ∧ ok (opn absent (excl_create_flags + O_NONBLOCK)) = true
  ∧ ok (opn absent (excl_create_flags + O_TRUNC + O_NONBLOCK)) = true
  ∧ ok (opn hfs (O_RDWR + O_NONBLOCK)) = true
  /- and the flags next to them are still declined, O_NONBLOCK or not -/
  ∧ opn hfs 256 = check_result.CheckUnmodeled                     /- O_NOCTTY -/
  ∧ opn hfs (256 + O_NONBLOCK) = check_result.CheckUnmodeled      /- O_NOCTTY|O_NONBLOCK -/
  ∧ opn hfs 1024 = check_result.CheckUnmodeled                    /- O_APPEND -/
  ∧ opn hfs (O_RDWR + O_APPEND) = check_result.CheckUnmodeled     /- O_RDWR|O_APPEND -/
  ∧ opn hfs (O_RDWR + O_EXCL) = check_result.CheckUnmodeled       /- O_EXCL without O_CREAT -/
  ∧ opn hfs (O_RDWR + O_DIRECTORY) = check_result.CheckUnmodeled/- O_RDWR|O_DIRECTORY -/
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE APPEND CREATE SHAPE, as three equalities and four declines.

    The first equality is the one only a literal can state, for the
    reason the O_NONBLOCK example above gives: it is an equality BETWEEN
    TWO FLAG WORDS, and a real run issues one word.

    The other two are what separates this shape from the clobbering one,
    and they are the reason the arm exists: on a path that is ALREADY
    THERE the open succeeds AND leaves the bytes alone, where
    O_WRONLY|O_CREAT|O_TRUNC would have emptied the file.  Both images
    are the same one, so the pair is a real contrast rather than two
    unrelated runs.

    The declines are the three O_APPEND spellings beside the modeled one
    ([Fs.Open.modeled_open_flags] names each and says why), plus
    O_APPEND on its own, which is O_RDONLY|O_APPEND and not this
    shape. -/
theorem openat_append_flag_word :
  let opn fs fl := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           mem_open_write (fun _ => none))
        (with_copyins [(8192, 2)] (mkEffect 3 [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let ok r := (match r with | check_result.CheckOk _ _ => true | _ => false ) ;
  let kept r := (match r with
                | check_result.CheckOk m _ => fs_lookup (m_fs m) [102]
                | _ => none
                ) ;
  let hfs : Fs.Fs := [([102], [104, 105])] ;
  let absent := [] ;
  /- the ignored bit is ignored on this arm too -/
  opn hfs (append_create_flags + O_NONBLOCK) = opn hfs append_create_flags
  ∧ ok (opn hfs (append_create_flags + O_NONBLOCK)) = true
  /- an ABSENT path is created empty, an EXISTING one keeps its bytes -/
  ∧ kept (opn absent append_create_flags) = some []
  ∧ kept (opn hfs append_create_flags) = some [104, 105]
  /- ...where the clobbering shape empties it -/
  ∧ kept (opn hfs wr_create_flags) = some []
  /- and the spellings next to it stay declined -/
  ∧ opn hfs (append_create_flags + O_TRUNC) = check_result.CheckUnmodeled
  ∧ opn hfs (append_create_flags + O_EXCL) = check_result.CheckUnmodeled
  ∧ opn hfs (O_WRONLY + O_APPEND) = check_result.CheckUnmodeled
  ∧ opn hfs (O_RDWR + O_CREAT + O_APPEND) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE SIX READ-WRITE WORDS, as the table the two bits decide.

    A real run issues one word, so every equation here that relates
    TWO flag words is one only a literal can state; and the
    file-content contrasts are stated against ONE image, so a pair is a
    real contrast rather than two unrelated runs.

    What the table says, and it is exactly [Fs.Open.openat_rdwr_spec]'s
    claim: O_TRUNC decides whether an EXISTING file keeps its bytes, and
    O_CREAT what an ABSENT name gets.  The declines beside them are the
    O_RDWR spellings [Fs.Open.modeled_open_flags] names and does not
    admit. -/
theorem openat_rdwr_flag_words :
  let opn fs fl := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           mem_open_write (fun _ => none))
        (with_copyins [(8192, 2)] (mkEffect 3 [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let ok r := (match r with | check_result.CheckOk _ _ => true | _ => false ) ;
  let kept r := (match r with
                | check_result.CheckOk m _ => fs_lookup (m_fs m) [102]
                | _ => none
                ) ;
  let hfs : Fs.Fs := [([102], [104, 105])] ;
  let absent := [] ;
  /- the ignored bit is ignored on this arm too -/
  opn hfs (O_RDWR + O_NONBLOCK) = opn hfs O_RDWR
  ∧ ok (opn hfs O_RDWR) = true
  /- O_TRUNC decides what an EXISTING file keeps -/
  ∧ kept (opn hfs O_RDWR) = some [104, 105]
  ∧ kept (opn hfs (O_RDWR + O_TRUNC)) = some []
  ∧ kept (opn hfs (O_RDWR + O_CREAT)) = some [104, 105]
  ∧ kept (opn hfs (O_RDWR + O_CREAT + O_TRUNC)) = some []
  /- O_CREAT decides what an ABSENT one gets: a fresh empty file on the
     three words that carry it, and nothing at all on the two that do
     not (those answer -ENOENT, below) -/
  ∧ kept (opn absent (O_RDWR + O_CREAT)) = some []
  ∧ kept (opn absent (O_RDWR + O_CREAT + O_TRUNC)) = some []
  ∧ kept (opn absent rdwr_excl_create_flags) = some []
  ∧ kept (opn absent (rdwr_excl_create_flags + O_TRUNC)) = some []
  /- and the fd it hands back is the READ-WRITE kind, at offset 0 -/
  ∧ (match opn hfs O_RDWR with
     | check_result.CheckOk m _ => fd_lookup (m_fds m) 3 = some (FdEntry.FdFileRW [102] 0)
     | _ => False
     )
  /- the spellings beside them stay declined -/
  ∧ opn hfs (O_RDWR + O_APPEND) = check_result.CheckUnmodeled
  ∧ opn hfs (O_RDWR + O_CREAT + O_APPEND) = check_result.CheckUnmodeled
  ∧ opn hfs (O_RDWR + O_EXCL) = check_result.CheckUnmodeled
  ∧ opn hfs (O_RDWR + O_TRUNC + O_EXCL) = check_result.CheckUnmodeled
  ∧ opn hfs (O_RDWR + O_DIRECTORY) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ERRNO HALF OF THE SAME TABLE, and the -EMFILE reject twins that
    pin it as DETERMINISTIC.

    Two answers here admit an [Fs.Open.openat_errnos] alternative and
    two do not, and no real run can separate them: a run is shown one
    answer, and the claim is that a kernel offering a DIFFERENT one is
    refused.  An open that can succeed may instead report the -EMFILE a
    real kernel raises before path resolution; an arm that reports a
    path-resolution errno insists on it, which is the approximation
    [Fs.Open.openat_spec]'s header records and the reason its
    hand-maintained list wants a twin per arm. -/
theorem openat_rdwr_errnos :
  let opn fs fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           mem_open_write (fun _ => none))
        (with_copyins [(8192, 2)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let hfs : Fs.Fs := [([102], [104, 105])] ;
  let absent := [] ;
  let base fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  /- no O_CREAT and no such name: the kernel's own -ENOENT -/
  opn absent O_RDWR (mkEffect (errno_ret ENOENT) [] [])
    = check_result.CheckOk (base absent) []
  ∧ opn absent (O_RDWR + O_TRUNC) (mkEffect (errno_ret ENOENT) [] [])
     = check_result.CheckOk (base absent) []
  /- the exclusive words on a name that IS there: -EEXIST -/
  ∧ opn hfs rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] [])
     = check_result.CheckOk (base hfs) []
  /- those three are deterministic, so a kernel that answered -EMFILE
     instead is REJECTED rather than admitted -/
  ∧ opn absent O_RDWR (mkEffect (errno_ret EMFILE) [] []) = check_result.CheckReject
  ∧ opn hfs rdwr_excl_create_flags (mkEffect (errno_ret EMFILE) [] [])
     = check_result.CheckReject
  /- while an open that can SUCCEED admits it -/
  ∧ opn hfs O_RDWR (mkEffect (errno_ret EMFILE) [] []) = check_result.CheckOk (base hfs) []
  ∧ opn absent (O_RDWR + O_CREAT) (mkEffect (errno_ret ENOMEM) [] [])
     = check_result.CheckOk (base absent) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A DIRECTORY REFERENCE, whose two answers come from two different
    kernel tests reached in the same call.  "." is [Uapi.dot_path]; the
    path bytes at 8192 are '.', NUL.

    Without O_CREAT nothing in [do_open]'s O_CREAT block runs and the
    -EISDIR is [may_open]'s S_IFDIR arm under [acc_mode & MAY_WRITE],
    which O_RDWR carries through [ACC_MODE] (fs/namei.c and fs/open.c,
    Linux v6.18.46).  With O_CREAT it is [do_open]'s own
    [d_is_dir(nd->path.dentry)] — unless O_EXCL is set, which is tested
    first and answers -EEXIST.  No real run separates the two -EISDIRs, and
    the -EEXIST is the one a reader gets backwards. -/
theorem openat_rdwr_dirref :
  let opn fl e := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (fun a => if bv_eqb a 8192 then some 46
                     else if bv_eqb a 8193 then some 0 else none)
           (fun _ => none))
        (with_copyins [(8192, 2)] (mkEffect (errno_ret e) [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) ;
  let base := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  opn O_RDWR EISDIR = check_result.CheckOk base []
  ∧ opn (O_RDWR + O_TRUNC) EISDIR = check_result.CheckOk base []
  ∧ opn (O_RDWR + O_CREAT) EISDIR = check_result.CheckOk base []
  ∧ opn (O_RDWR + O_CREAT + O_TRUNC) EISDIR = check_result.CheckOk base []
  ∧ opn rdwr_excl_create_flags EEXIST = check_result.CheckOk base []
  /- the exclusive word does NOT answer -EISDIR, and none of the other
     four answers -EEXIST -/
  ∧ opn rdwr_excl_create_flags EISDIR = check_result.CheckReject
  ∧ opn O_RDWR EEXIST = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! The interpreted file system, end to end: openat(AT_FDCWD, "f",
    O_WRONLY|O_CREAT|O_TRUNC, 0644) creating "f" (path bytes at 8192:
    'f', NUL), then write(3, "hi", 2) — and the file contents appear in
    the final model.  This is the readable statement of what the model
    does. -/

def ftruncate_dangling_model : Model :=
  mkModel [(3, FdEntry.FdFileW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    []

theorem ftruncate_on_a_dangling_fd_is_unmodeled :
  check_syscall (SyscallInput.mkInput 46 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) ftruncate_dangling_model
  = check_result.CheckUnmodeled
:= by rfl

/- ================================================ faccessat (48)

   Four claims.  One needs a file-system image no modeled syscall can
   build.  The other three are the mode-before-pathname order and its
   ledger halves — an -EINVAL that read nothing, a 0 that must have. -/

/-! Path bytes at 8192 for the faccessat examples: 'a', NUL. -/
def fa_mem_name_a : word → Option byte :=
  fun a => if bv_eqb a 8192 then some 97        /- 'a' -/
           else if bv_eqb a 8193 then some 0    /- NUL -/
           else none

/-! A key living UNDER a name means reality has a DIRECTORY the flat map
    only implies, and F_OK of a directory is 0 where the map would answer
    -ENOENT.  So [Fs.Namei.fs_under] declines it.  This is the one
    faccessat decline only the starting image can set up: no modeled
    syscall puts a separator in a key.  The guard [unlinkat] uses to avoid a wrong ERRNO is used
    here to avoid a wrong exists-or-not. -/
theorem faccessat_implied_directory_unmodeled :
  check_syscall
    (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 0, 0, 0, 0] fa_mem_name_a (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []), ([97, 47, 98], [104])] IEof))
  = check_result.CheckUnmodeled
:= by rfl

/-! The contrast, so the guard is a COMPONENT prefix and not a byte
    prefix: "ab" does not live under "a", so "a" is an ordinary present
    key and F_OK of it is 0, with the model left exactly as it was —
    faccessat changes nothing. -/
theorem faccessat_byte_prefix_is_not_a_directory :
  (match check_syscall
          (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 0, 0, 0, 0] fa_mem_name_a (fun _ => none))
          (with_copyins [(8192, 2)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input [([97], []), ([97, 98], [104])] IEof)) with
  | check_result.CheckOk m [] => m_fs m = [([97], []), ([97, 98], [104])]
  | _ => False
  )
:= by rfl

/-! THE MODE BEATS THE PATHNAME FETCH, which is the sharpest claim
    [Fs.Open.faccessat_spec] makes: fs/open.c [do_faccessat] (v6.18.46)
    tests [mode & ~S_IRWXO] before [getname], so a bad mode with an
    UNREADABLE path is -EINVAL and never -EFAULT.  Here the pathname is
    at an address no byte answers at, and the answer is still -EINVAL with an
    empty ledger.  A spec that fetched first would answer -EFAULT and
    this would reject. -/
theorem faccessat_bad_mode_beats_an_unreadable_path :
  check_syscall
    (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 8, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof)) []
:= by rfl

/-! ...and because the mode is decided before [user_path_at], that arm
    reads NO user memory: a ledger claimed there is a read the kernel did
    not perform.  This is the case a spec that wrapped the whole body in
    [record_copyins] gets wrong — it would EXPECT this range and accept. -/
theorem faccessat_bad_mode_records_no_copyin :
  check_syscall
    (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 8, 0, 0, 0] fa_mem_name_a (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret EINVAL) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = check_result.CheckReject
:= by rfl

/-! Past the mode test the ledger is REQUIRED: the F_OK call really did
    read the path, so denying it is a rejection.  These two differ in the
    mode word alone, and the ledger obligation flips with it. -/
theorem faccessat_existence_needs_the_copyin :
  check_syscall
    (SyscallInput.mkInput 48 [AT_FDCWD, 8192, 0, 0, 0, 0] fa_mem_name_a (fun _ => none))
    (mkEffect 0 [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = check_result.CheckReject
:= by rfl

/- ================================ openat's flat-namespace declines

   [Fs.Open.openat_resolved_spec] declines a pathname with a separator
   in it, because the flat file system has no path walk and so cannot
   reach any of the answers one produces; ".." it ANSWERS, being a
   directory reference the walk settles on its own, and so do the two
   paths [Fs.Open.openat_sep_spec] names: /etc/localtime, on a declared
   assumption rather than a walk, and /dev/null, whose answers come from
   its driver (their examples follow the declines).  These are claims
   about that boundary which a real run cannot make: a run cannot vary
   the KERNEL'S answer (it gets the one the kernel gives) or build a
   file-system image whose keys hold a separator (no modeled syscall
   puts one there). -/

/-! Path bytes at 8192, NUL-terminated, for the examples below. -/
def open_path_mem (bs : List Int) : word → Option byte :=
  fun a => if (zleb 8192 (bv_unsigned a))
           then nth_error (List.map (fun z => Z_to_bv 8 z) (bs ++ [0]))
                  (Int.toNat (bv_unsigned a - 8192))
           else none

/-! THE DECLINE DOES NOT DEPEND ON WHAT THE KERNEL SAID, which is the
    half no real run reaches: a run is shown one answer, and the claim
    here is over two that could not both be right.  The write-create
    open of "/a" is [CheckUnmodeled] when the kernel is offered as having
    SUCCEEDED at fd 3 and when it is offered as having failed -ENOENT —
    so the model is not quietly agreeing with one of them.

    Without the guard the first of these would be [CheckOk]: a create
    that tested the pathname against "." and nothing else would bind
    fd 3 and record a key literally spelled "/a" where Linux resolves a
    directory it never looked in.  That is the unsound admission this
    guard prevents, and it is why the pair below is stated as a pair. -/
theorem openat_absolute_create_unmodeled :
  let opn eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
           (open_path_mem [47, 97]) (fun _ => none))
        (with_copyins [(8192, 3)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) ;
  opn (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckUnmodeled
:= by constructor <;> rfl

/-! THE CONTROL, and the reason the pair above is evidence of anything.
    The identical call on a slash-free name is not declined: it succeeds
    at the lowest free fd and the key appears in the model's file system.
    So the guard discriminates on the PATH SHAPE — it does not disable
    the create arm, and a run of nothing but declines would not show
    that. -/
theorem openat_plain_create_still_mints_the_key :
  (match check_syscall
          (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
             (open_path_mem [97]) (fun _ => none))
          (with_copyins [(8192, 2)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) with
  | check_result.CheckOk m [] => m_fs m = [([Z_to_bv 8 97], [])]
  | _ => False
  )
:= by rfl

/- ================================ an implied directory under the create words

   [Fs.Open.openat_create_spec] and its siblings test
   [path_is_dirref p || fs_under (m_fs m) p]: a plain name some key of
   the image lives under is a directory the flat map only implies, and
   an O_CREAT open of it is the deterministic answer [do_open] gives a
   positive directory dentry — -EEXIST under O_EXCL, -EISDIR otherwise
   (fs/namei.c, Linux v6.18.46).  No modeled syscall creates a
   directory, so only the starting image can set this up, and the
   `reject` half of each claim is pinned here as a literal beside the
   accepted answer. -/

/-! THE CLOBBERING CREATE OF AN IMPLIED DIRECTORY IS -EISDIR, and the
    model is untouched by it: with "a/b" in the image, the
    O_WRONLY|O_CREAT|O_TRUNC open of "a" accepts -EISDIR, REFUSES the
    descriptor the kernel could be offered as having minted (the answer
    before this arm), and the control — the same call on "c", which
    nothing lives under — still creates its key. -/
theorem openat_implied_directory_create_eisdir :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let under : Fs.Fs := [([Z_to_bv 8 97, Z_to_bv 8 47, Z_to_bv 8 98], [104])] ;
  let opn name eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
           (open_path_mem [name]) (fun _ => none))
        (with_copyins [(8192, 2)] eff) (m0 under) ;
  opn 97 (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn 97 (mkEffect 3 [] []) = check_result.CheckReject
  ∧ (match opn 99 (mkEffect 3 [] []) with
     | check_result.CheckOk m [] => m_fs m = fs_set under [Z_to_bv 8 99] []
     | _ => False
     )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE TEST IS A COMPONENT PREFIX, NOT A BYTE PREFIX, AND NOT EQUALITY.
    [Fs.Namei.fs_under] asks whether some key continues [p] with a
    separator, so an image holding "ab" does not make "a" a directory —
    the create of "a" mints its key beside "ab", as before — and an
    image holding "a" itself is the ordinary truncating create, the file
    emptied and no -EISDIR: the offered -EISDIR is refused on both.  The
    openat twin of [faccessat_byte_prefix_is_not_a_directory]. -/
theorem openat_byte_prefix_and_exact_key_still_create :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let sibling : Fs.Fs := [([Z_to_bv 8 97, Z_to_bv 8 98], [104])] ;
  let exact : Fs.Fs := [([Z_to_bv 8 97], [104])] ;
  let opn fs eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
           (open_path_mem [97]) (fun _ => none))
        (with_copyins [(8192, 2)] eff) (m0 fs) ;
  (match opn sibling (mkEffect 3 [] []) with
  | check_result.CheckOk m [] => m_fs m = fs_set sibling [Z_to_bv 8 97] []
  | _ => False
  )
  ∧ opn sibling (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckReject
  ∧ (match opn exact (mkEffect 3 [] []) with
     | check_result.CheckOk m [] => m_fs m = [([Z_to_bv 8 97], [])]
     | _ => False
     )
  ∧ opn exact (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE EXCLUSIVE CREATE OF AN IMPLIED DIRECTORY IS -EEXIST, not
    -EISDIR: [do_open] tests O_EXCL against [FMODE_CREATED] before it
    tests [d_is_dir], the same order that makes "." -EEXIST under this
    word.  The descriptor is refused, and the control on "c" creates. -/
theorem openat_implied_directory_excl_eexist :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let under : Fs.Fs := [([Z_to_bv 8 97, Z_to_bv 8 47, Z_to_bv 8 98], [104])] ;
  let opn name eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 excl_create_flags, 420, 0, 0]
           (open_path_mem [name]) (fun _ => none))
        (with_copyins [(8192, 2)] eff) (m0 under) ;
  opn 97 (mkEffect (errno_ret EEXIST) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn 97 (mkEffect 3 [] []) = check_result.CheckReject
  ∧ (match opn 99 (mkEffect 3 [] []) with
     | check_result.CheckOk m [] => m_fs m = fs_set under [Z_to_bv 8 99] []
     | _ => False
     )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE OTHER WRITE-CAPABLE WORDS AGREE, each through its own arm: the
    append shape and the read-write shapes with and without O_CREAT and
    O_TRUNC answer -EISDIR (the O_CREAT-free ones through [may_open]'s
    S_IFDIR arm rather than [do_open]'s [d_is_dir], the same errno by
    a different route), and the exclusive read-write shape answers
    -EEXIST. -/
theorem openat_implied_directory_other_write_words :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let under : Fs.Fs := [([Z_to_bv 8 97, Z_to_bv 8 47, Z_to_bv 8 98], [104])] ;
  let opn fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem [97]) (fun _ => none))
        (with_copyins [(8192, 2)] eff) (m0 under) ;
  opn append_create_flags (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn (O_RDWR + O_CREAT) (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn (O_RDWR + O_CREAT + O_TRUNC) (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn O_RDWR (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn (O_RDWR + O_TRUNC) (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = check_result.CheckOk (m0 under) []
  ∧ opn (O_RDWR + O_CREAT) (mkEffect 3 [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A KEY SPELLED WITH A SEPARATOR comes only from the starting image —
    no modeled syscall puts a separator in a key — and it is the one
    where answering would look
    most defensible: the map HOLDS "a/b", so a read of "a/b" could just
    return it.  It is declined anyway, because whether that key is
    reachable depends on "a" being a directory, which the map does not
    say.  The same guard, and the same reason, as
    [faccessat_implied_directory_unmodeled] above. -/
theorem openat_slash_key_in_image_unmodeled :
  check_syscall
    (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 0, 0, 0]
       (open_path_mem [97, 47, 98]) (fun _ => none))
    (with_copyins [(8192, 4)] (mkEffect 3 [] []))
    (init_model [] 0 0 demo_sp demo_limit
       (demo_input [([Z_to_bv 8 97, Z_to_bv 8 47, Z_to_bv 8 98], [104])] IEof))
  = check_result.CheckUnmodeled
:= by rfl

/- ================================ "/etc/localtime", the answered exception

   [Fs.Open.openat_localtime_spec] answers -ENOENT for exactly this path
   under a MAINTAINER-DECLARED assumption about the image (the image has
   no /etc/localtime), and fails closed wherever
   the assumption does not reach.  These pin both halves, and the edges
   of the byte string the assumption was declared for. -/

/-! The bytes of "/etc/localtime". -/
def localtime_bytes : List Int :=
  [47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101]

/-! THE -ENOENT IS AN ANSWER, NOT A DECLINE, and the model insists on
    it: every O_CREAT-free word the model interprets is a [CheckOk] in
    the unchanged model when the kernel reports -ENOENT, and a kernel
    that reports a descriptor instead is REJECTED.  The
    O_CLOEXEC|O_NONBLOCK row is the word musl's [__map_file] issues for
    this path (musl 1.2.6, src/time/__map_file.c); both bits are in
    [Fs.Open.open_ignored_flags], so it is the O_RDONLY arm.  Beside
    them, every word with O_CREAT is [CheckUnmodeled]: Linux would
    create the file under /etc, and the model has no /etc to create it
    in. -/
theorem openat_localtime_enoent :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let opn fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem localtime_bytes) (fun _ => none))
        (with_copyins [(8192, 15)] eff) m0 ;
  let enoent := mkEffect (errno_ret ENOENT) [] [] ;
  /- without O_CREAT: -ENOENT, an Ok, whatever the access mode -/
  opn 0 enoent = check_result.CheckOk m0 []
  ∧ opn (0 + O_CLOEXEC) enoent = check_result.CheckOk m0 []
  ∧ opn (O_CLOEXEC + O_NONBLOCK) enoent = check_result.CheckOk m0 []
  ∧ opn O_RDWR enoent = check_result.CheckOk m0 []
  ∧ opn (O_RDWR + O_TRUNC) enoent = check_result.CheckOk m0 []
  ∧ opn O_DIRECTORY enoent = check_result.CheckOk m0 []
  /- a claimed success is refused: the answer is deterministic -/
  ∧ opn 0 (mkEffect 3 [] []) = check_result.CheckReject
  ∧ opn 0 (mkEffect (errno_ret EACCES) [] []) = check_result.CheckReject
  /- with O_CREAT: fail closed, in every spelling the model admits -/
  ∧ opn wr_create_flags enoent = check_result.CheckUnmodeled
  ∧ opn excl_create_flags enoent = check_result.CheckUnmodeled
  ∧ opn append_create_flags enoent = check_result.CheckUnmodeled
  ∧ opn (O_RDWR + O_CREAT) enoent = check_result.CheckUnmodeled
  ∧ opn rdwr_excl_create_flags enoent = check_result.CheckUnmodeled
  ∧ opn wr_create_flags (mkEffect 3 [] []) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS THE FILE.  A map
    holding the key "/etc/localtime", or a key under it, describes an
    image the declaration was not made about, and the open is declined
    rather than answered from the map — whatever the kernel is offered
    as having said, so the model is not quietly siding with one
    answer. -/
theorem openat_localtime_in_image_unmodeled :
  let opn fs eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
           (open_path_mem localtime_bytes) (fun _ => none))
        (with_copyins [(8192, 15)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let key := List.map (fun z => Z_to_bv 8 z) localtime_bytes ;
  let enoent := mkEffect (errno_ret ENOENT) [] [] ;
  opn [(key, [104])] enoent = check_result.CheckUnmodeled
  ∧ opn [(key, [104])] (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [(key ++ [Z_to_bv 8 47, Z_to_bv 8 120], [104])] enoent = check_result.CheckUnmodeled
  ∧ opn [(key ++ [Z_to_bv 8 47, Z_to_bv 8 120], [104])] (mkEffect 3 [] [])
     = check_result.CheckUnmodeled
  /- the control: an unrelated key leaves the answer in place -/
  ∧ opn [([Z_to_bv 8 97], [104])] enoent
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit
                  (demo_input [([Z_to_bv 8 97], [104])] IEof)) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE MATCH IS EXACT.  Linux resolves "/etc//localtime" and
    "//etc/localtime" to the same file, and a prefix or an extension of
    the name to a different one; the model identifies none of them with
    the declared path, so each is the separator decline the arm sits in
    front of.  The last conjunct is the control that keeps the others
    from being satisfied by a model that declines everything. -/
theorem openat_localtime_match_is_exact :
  let opn bs n := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] (mkEffect (errno_ret ENOENT) [] []))
        (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) ;
  opn ([47, 101, 116, 99, 47, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101])
       16 = check_result.CheckUnmodeled
  ∧ opn ([47, 47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109, 101])
       16 = check_result.CheckUnmodeled
  ∧ opn ([47, 101, 116, 99, 47, 108, 111, 99, 97, 108, 116, 105, 109])
       14 = check_result.CheckUnmodeled
  ∧ opn (localtime_bytes ++ [115]) 16 = check_result.CheckUnmodeled
  ∧ opn localtime_bytes 15
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/- ================================ "/dev/null", the answered device

   [Fs.Open.openat_devnull_spec] answers the exact byte string
   "/dev/null" ahead of the separator decline and mints
   [State.FdDevNull], the kind whose every answer comes from
   [null_fops] (drivers/char/mem.c) rather than from the file system.
   These pin the open under each admitted word, the open, write, read,
   close sequence, and the answers the
   kind forces at every fd-kind dispatch site outside fs/open.c, which
   have nowhere else to be pinned. -/

/-! The bytes of "/dev/null". -/
def devnull_bytes : List Int := [47, 100, 101, 118, 47, 110, 117, 108, 108]

def devnull_m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)

/-! THE OPEN, under every admitted word.  The access mode the word
    names is what the entry records; the O_TRUNC of the clobbering word
    and the O_APPEND of the append word are inert on the device, so both
    mint the write-only entry; the O_EXCL words are -EEXIST and the
    O_DIRECTORY word -ENOTDIR, deterministically (a claimed success is
    rejected on those two); and the image is untouched by every one of
    them, which is the whole point of a device over a key. -/
theorem devnull_open_by_word :
  let opn fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem devnull_bytes) (fun _ => none))
        (with_copyins [(8192, 10)] eff) devnull_m0 ;
  let minted fl rd wr :=
        (match opn fl (mkEffect 3 [] []) with
        | check_result.CheckOk m [] => fd_lookup (m_fds m) 3 = some (FdEntry.FdDevNull rd wr)
                          ∧ m_fs m = []
        | _ => False
        ) ;
  minted 0 true false
  ∧ minted (0 + O_CLOEXEC) true false
  ∧ minted wr_create_flags false true
  ∧ minted append_create_flags false true
  ∧ minted O_RDWR true true
  ∧ minted (O_RDWR + O_CREAT + O_TRUNC) true true
  ∧ opn excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = check_result.CheckOk devnull_m0 []
  ∧ opn rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = check_result.CheckOk devnull_m0 []
  ∧ opn O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] []) = check_result.CheckOk devnull_m0 []
  ∧ opn excl_create_flags (mkEffect 3 [] []) = check_result.CheckReject
  ∧ opn O_DIRECTORY (mkEffect 3 [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS A FILE UNDER THE
    NAME, or a key under it, and THE MATCH IS EXACT: each of those is the
    ordinary separator decline, whatever the kernel is offered as having
    said.  The last conjunct is the control. -/
theorem devnull_open_declines :
  let opn fs bs n eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let key := List.map (fun z => Z_to_bv 8 z) devnull_bytes ;
  opn [(key, [104])] devnull_bytes 10 (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [(key, [104])] devnull_bytes 10 (mkEffect (errno_ret ENOENT) [] [])
     = check_result.CheckUnmodeled
  ∧ opn [(key ++ [Z_to_bv 8 47, Z_to_bv 8 120], [104])] devnull_bytes 10
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [] ([47, 100, 101, 118, 47, 47, 110, 117, 108, 108]) 11
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [] ([47, 100, 101, 118, 47, 110, 117, 108]) 9
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ ((match opn [] devnull_bytes 10 (mkEffect 3 [] []) with
      | check_result.CheckOk _ [] => True | _ => False ))
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A table with one descriptor of each access mode, for the dispatch
    sites below: 3 read-only, 4 write-only, 5 read-write. -/
def devnull_model : Model :=
  mkModel [(0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
           (3, FdEntry.FdDevNull true false), (4, FdEntry.FdDevNull false true),
           (5, FdEntry.FdDevNull true true)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof []

/-! THE COMMON SHAPE: open write-only, write, read, close.  The write
    returns the count from an UNMAPPED buffer with an EMPTY ledger —
    [write_null] reads no byte, so a claimed copy-in is rejected — and
    the read on the same descriptor is the kernel's -EBADF.  Then the
    read-only and read-write descriptors: a read is 0 into a buffer no
    page backs, with nothing written, and a write through the read-only
    one is -EBADF. -/
theorem devnull_open_write_read_close :
  let call no args eff m := check_syscall
        (SyscallInput.mkInput no args (fun _ => none) (fun _ => none)) eff m ;
  (match check_syscall
          (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
             (open_path_mem devnull_bytes) (fun _ => none))
          (with_copyins [(8192, 10)] (mkEffect 3 [] [])) devnull_m0 with
  | check_result.CheckOk m1 [] =>
      call 64 [3, 4096, 5, 0, 0, 0] (mkEffect 5 [] []) m1 = check_result.CheckOk m1 []
      ∧ call 64 [3, 4096, 5, 0, 0, 0]
           (with_copyins [(4096, 5)] (mkEffect 5 [] [])) m1 = check_result.CheckReject
      ∧ call 64 [3, 4096, 5, 0, 0, 0] (mkEffect 4 [] []) m1 = check_result.CheckReject
      ∧ call 63 [3, 4096, 16, 0, 0, 0] (mkEffect (errno_ret EBADF) [] []) m1
         = check_result.CheckOk m1 []
      ∧ call 57 [3, 0, 0, 0, 0, 0] (mkEffect 0 [] []) m1 = check_result.CheckOk devnull_m0 []
  | _ => False
  )
  ∧ call 63 [3, 4096, 16, 0, 0, 0] (mkEffect 0 [] []) devnull_model
     = check_result.CheckOk devnull_model []
  ∧ call 63 [5, 4096, 16, 0, 0, 0] (mkEffect 0 [] []) devnull_model
     = check_result.CheckOk devnull_model []
  ∧ call 63 [3, 4096, 16, 0, 0, 0] (mkEffect 1 [(4096, [104])] [])
       devnull_model = check_result.CheckReject
  ∧ call 64 [3, 4096, 5, 0, 0, 0] (mkEffect (errno_ret EBADF) [] []) devnull_model
     = check_result.CheckOk devnull_model []
  ∧ call 64 [5, 4096, 5, 0, 0, 0] (mkEffect 5 [] []) devnull_model
     = check_result.CheckOk devnull_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE DISPATCH SITES.  [lseek] is 0 for every whence and offset
    ([null_lseek]), and a claimed repositioning is rejected; [pread64]
    is 0 and [pwrite64] the count at any position; [fsync] and
    [ftruncate] are -EINVAL; [getdents64] is -ENOTDIR; [dup] copies the
    entry; [fcntl] F_SETFD is 0 and F_GETFL declines; [ioctl] answers
    TCGETS with -ENOTTY (the kind's table has no [.unlocked_ioctl]) and
    still declines a request outside the terminal-only eight, and
    [flock] fails closed; [fstat] delivers, and its own example
    follows. -/
theorem devnull_dispatch_sites :
  let call no args eff := check_syscall
        (SyscallInput.mkInput no args (fun _ => none) (fun _ => none)) eff devnull_model ;
  let ok eff := call 62 [5, 3, 0, 0, 0, 0] eff ;
  ok (mkEffect 0 [] []) = check_result.CheckOk devnull_model []
  ∧ ok (mkEffect 3 [] []) = check_result.CheckReject
  ∧ call 62 [5, 7, 2, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk devnull_model []   /- SEEK_END -/
  ∧ call 62 [5, 0, 4, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk devnull_model []   /- SEEK_HOLE -/
  ∧ call 67 [3, 4096, 16, 100, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk devnull_model []
  ∧ call 68 [4, 4096, 5, 100, 0, 0] (mkEffect 5 [] []) = check_result.CheckOk devnull_model []
  ∧ call 82 [4, 0, 0, 0, 0, 0] (mkEffect (errno_ret EINVAL) [] []) = check_result.CheckOk devnull_model []
  ∧ call 46 [4, 0, 0, 0, 0, 0] (mkEffect (errno_ret EINVAL) [] []) = check_result.CheckOk devnull_model []
  ∧ call 61 [3, 4096, 1024, 0, 0, 0] (mkEffect (errno_ret ENOTDIR) [] [])
     = check_result.CheckOk devnull_model []
  ∧ ((match call 23 [5, 0, 0, 0, 0, 0] (mkEffect 6 [] []) with
      | check_result.CheckOk m [] => fd_lookup (m_fds m) 6 = some (FdEntry.FdDevNull true true)
      | _ => False ))
  ∧ call 25 [5, F_SETFD, 1, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk devnull_model []
  ∧ call 25 [5, F_GETFL, 0, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckUnmodeled
  ∧ call 80 [5, 4096, 0, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckUnmodeled
     /- an fstat into a destination no page backs: the partial
        [copy_to_user] decline, before any byte is judged — the
        delivering arm is the example after this one -/
  ∧ call 29 [5, TCGETS, 4096, 0, 0, 0] (mkEffect (errno_ret ENOTTY) [] [])
     = check_result.CheckOk devnull_model []
  ∧ call 29 [5, Z_to_bv 64 21537, 4096, 0, 0, 0] (mkEffect 0 [] [])
     = check_result.CheckUnmodeled   /- FIONBIO 0x5421: outside the eight, still declined -/
  ∧ call 32 [5, 2, 0, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A [struct stat] for the examples: the device's asserted members as
    given, zero everywhere else. -/
def dev_stat (mode rdev size : Int) : List byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 mode ++ Z_to_le_bytes 12 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 size
  ++ Z_to_le_bytes 72 0

/-! fstat ON /dev/null IS ANSWERED, AND THE DEVICE'S MEMBERS ARE ASSERTED.
    A delivered S_IFCHR with [st_rdev] 1:3 and a zero size is accepted
    and PINNED under [devnull_path]; the regular-file answer a plain key
    would produce (S_IFREG, the recorded length) is rejected, as
    are the right type with the wrong device number and the right device
    with a nonzero size.  A second fstat must repeat the pin's stable
    members: the same bytes are accepted again, and bytes differing in
    the inode are rejected.  The destination is 128 writable bytes at
    4096. -/
theorem devnull_fstat_asserts_the_device :
  let wmem := fun a => if (zleb 4096 (bv_unsigned a) && zltb (bv_unsigned a) 4224)
                       then some (Z_to_bv 8 0) else none ;
  let call m eff := check_syscall
        (SyscallInput.mkInput 80 [5, 4096, 0, 0, 0, 0] (fun _ => none) wmem) eff m ;
  let good := dev_stat S_IFCHR DEVNULL_RDEV 0 ;
  let deliver bs := mkEffect 0 [(4096, bs)] [] ;
  ((match call devnull_model (deliver good) with
   | check_result.CheckOk m [] =>
       statpin_lookup (m_statpins m) devnull_path = some good
       ∧ call m (deliver good) = check_result.CheckOk m []
       ∧ call m (deliver (Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 7
                            ++ List.drop 16 good)) = check_result.CheckReject
   | _ => False
   ))
  ∧ call devnull_model (deliver (dev_stat S_IFREG 0 5)) = check_result.CheckReject
  ∧ call devnull_model (deliver (dev_stat S_IFCHR 0 0)) = check_result.CheckReject
  ∧ call devnull_model (deliver (dev_stat S_IFCHR DEVNULL_RDEV 5)) = check_result.CheckReject
  ∧ call devnull_model (mkEffect 0 [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/- ================================ "/dev/urandom", the declared stream

   [Fs.Open.openat_urandom_spec] answers the exact byte string
   "/dev/urandom" ahead of the separator decline and mints
   [State.FdUrandom], whose reads hand out the run's DECLARED stream
   ([State.in_urandom]: arbitrary but fixed, a parameter of the
   execution like argv and envp).  These pin the open under each word,
   the open, read, close sequence with a stream long enough, the decline
   when the stream runs out, the answers at every dispatch site, the
   fstat delivery, and — the point of the declared stream — that two
   models seeded from one stream read the same bytes. -/

/-! The bytes of "/dev/urandom". -/
def urandom_bytes : List Int :=
  [47, 100, 101, 118, 47, 117, 114, 97, 110, 100, 111, 109]

/-! A declared stream from a byte list, for the fixtures. -/
def urandom_stream (l : List Int) : InputStream :=
  (match l with
  | [] => IEof
  | z :: r => ICons (Z_to_bv 8 z) (urandom_stream r)
  )

/-! A run whose device declares sixteen bytes. -/
def urandom_decl : List Int :=
  [17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255, 0]

def urandom_m0 : Model :=
  with_urandom (urandom_stream urandom_decl)
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))

/-! THE OPEN, under every word: O_RDONLY (with or without O_CLOEXEC)
    mints the read-only kind and leaves the image alone; the O_EXCL
    words are -EEXIST and the O_DIRECTORY word -ENOTDIR (a claimed
    success is rejected on both); the WRITE words — clobbering,
    appending, read-write — are declined, not answered. -/
theorem urandom_open_by_word :
  let opn fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem urandom_bytes) (fun _ => none))
        (with_copyins [(8192, 13)] eff) urandom_m0 ;
  let minted fl :=
        (match opn fl (mkEffect 3 [] []) with
        | check_result.CheckOk m [] => fd_lookup (m_fds m) 3 = some FdEntry.FdUrandom
                          ∧ m_fs m = []
                          ∧ m_urandom m = urandom_stream urandom_decl
        | _ => False
        ) ;
  minted 0
  ∧ minted (0 + O_CLOEXEC)
  ∧ opn excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = check_result.CheckOk urandom_m0 []
  ∧ opn rdwr_excl_create_flags (mkEffect (errno_ret EEXIST) [] []) = check_result.CheckOk urandom_m0 []
  ∧ opn O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] []) = check_result.CheckOk urandom_m0 []
  ∧ opn excl_create_flags (mkEffect 3 [] []) = check_result.CheckReject
  ∧ opn O_DIRECTORY (mkEffect 3 [] []) = check_result.CheckReject
  ∧ opn wr_create_flags (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn append_create_flags (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn O_RDWR (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn (O_RDWR + O_CREAT + O_TRUNC) (mkEffect 3 [] []) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ASSUMPTION DOES NOT REACH AN IMAGE THAT SHIPS A FILE UNDER THE
    NAME, or a key under it, and THE MATCH IS EXACT: "/dev//urandom"
    and "/dev/random" — a different device the ladder does not name —
    are the ordinary separator decline.  The last conjunct is the
    control. -/
theorem urandom_open_declines :
  let opn fs bs n eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof)) ;
  let key := List.map (fun z => Z_to_bv 8 z) urandom_bytes ;
  opn [(key, [104])] urandom_bytes 13 (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [(key ++ [Z_to_bv 8 47, Z_to_bv 8 120], [104])] urandom_bytes 13
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [] ([47, 100, 101, 118, 47, 47, 117, 114, 97, 110, 100, 111, 109]) 14
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [] ([47, 100, 101, 118, 47, 114, 97, 110, 100, 111, 109]) 12
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ ((match opn [] urandom_bytes 13 (mkEffect 3 [] []) with
      | check_result.CheckOk _ [] => True | _ => False ))
:= by (try dsimp only); (repeat constructor) <;> rfl

/- ================================ the images those three declines are about

   [openat_localtime_in_image_unmodeled], [devnull_open_declines] and
   [urandom_open_declines] above each pin what the arm does on an image
   that ships the device's name as a key: it declines.  That answer is
   the courtesy the arms' comments call it, and the pins stay — an
   [Fs.Fs] is a type, and a checker handed one of those maps really does
   answer [CheckUnmodeled].

   The other half is here: such a map is not an image a run can have.
   [Run.valid_input] carries
   [Fs.fs_keys_relative] over [State.in_image_fs], so a
   statement quantified over valid inputs never reaches those declines,
   and the pins below say so at both ends — the pathological image is
   refused by the validity predicate, and an image the predicate ADMITS
   answers the open.

   THE CONTROL IS THE POINT.  "Not a valid input" is easy to prove for
   the wrong reason: [Cases.Prelude.demo_input] has an empty argv, which
   [Run.valid_argv] already refuses, so a refutation over it would hold
   with no premise about keys at all.  So these run over a fixture with
   the one empty argument [Run.valid_argv] asks for, and each refutation
   is paired with the SAME fixture over a key that differs by the
   leading separator alone, which is admitted. -/

/-! The launchable fixture: [Cases.Prelude.demo_input_tmp] with
    [Run.valid_argv]'s one empty argument, so that [Run.valid_input] of
    it turns on the image and on the declaration and on nothing else. -/
def image_input_tmp (fs0 tmp0 : Fs.Fs) : ProcInput :=
  /- [valid_input] asks the declared /dev/urandom stream to be infinite, so
     the image inputs declare [default_urandom] (as [Cases.Prelude]'s
     fixture does) rather than [IEof]. -/
  ProcInput.mkProcInput_full [[]] [] fs0 IEof demo_uid demo_gid demo_groups net_silent
                   default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48 default_urandom tmp0

def image_input (fs0 : Fs.Fs) : ProcInput := image_input_tmp fs0 []

/-! The three device names as keys, and the same three with the leading
    separator dropped — "dev/null", "etc/localtime", "dev/urandom",
    which are ordinary cwd-relative names a launch really can hand a
    process, separators and all. -/
def key_of (bs : List Int) : Fs.path := List.map (fun z => Z_to_bv 8 z) bs

def devnull_key : Fs.path := key_of devnull_bytes
def localtime_key : Fs.path := key_of localtime_bytes
def urandom_key : Fs.path := key_of urandom_bytes

def devnull_relative_key : Fs.path := key_of (List.tail devnull_bytes)
def localtime_relative_key : Fs.path := key_of (List.tail localtime_bytes)
def urandom_relative_key : Fs.path := key_of (List.tail urandom_bytes)

/-! [Fs.valid_fs]'s NUL-free clause, decided rather than case-split: on a
    concrete key the membership is the boolean test [State.tmp_nul_free]
    already runs, so [vm_compute] closes it. -/
theorem not_in_bytes_of_existsb : ∀ (b : byte) (l : List byte),
  l.any (fun c => bv_eqb c b) = false → b ∉ l := by
  intro b l H hmem
  have h1 : l.any (fun c => bv_eqb c b) = true := by
    rw [List.any_eq_true]
    exact ⟨b, hmem, bv_eqb_refl b⟩
  rw [h1] at H
  exact Bool.noConfusion H

/-! An image keyed by a device name is not [Fs.fs_keys_relative]. -/
theorem device_key_images_are_not_relative :
  ¬ fs_keys_relative [(devnull_key, [Z_to_bv 8 104])]
  ∧ ¬ fs_keys_relative [(localtime_key, [Z_to_bv 8 104])]
  ∧ ¬ fs_keys_relative [(urandom_key, [Z_to_bv 8 104])] := by
  refine ⟨?_, ?_, ?_⟩
  · intro H; exact (H (devnull_key, [Z_to_bv 8 104]) (by simp)) rfl
  · intro H; exact (H (localtime_key, [Z_to_bv 8 104]) (by simp)) rfl
  · intro H; exact (H (urandom_key, [Z_to_bv 8 104]) (by simp)) rfl

/-! …so no run has one: the fixture over it is refused by
    [Run.valid_input], and refused THROUGH the keys clause — the
    conjunct the pattern below names is the one that fails. -/
theorem device_key_inputs_are_not_valid :
  ¬ valid_input (image_input [(devnull_key, [Z_to_bv 8 104])])
  ∧ ¬ valid_input (image_input [(localtime_key, [Z_to_bv 8 104])])
  ∧ ¬ valid_input (image_input [(urandom_key, [Z_to_bv 8 104])]) := by
  obtain ⟨Hd, Hl, Hu⟩ := device_key_images_are_not_relative
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _, _, Hk, _⟩; exact Hd Hk
  · rintro ⟨_, _, _, Hk, _⟩; exact Hl Hk
  · rintro ⟨_, _, _, Hk, _⟩; exact Hu Hk

/-! THE CONTROL.  Drop the leading separator and the very same fixture
    IS valid — with a declared private /tmp beside it, so the seeded
    image really does carry the absolute key "/tmp/f" and the clause is
    seen to be about the PRE-SEED image rather than about the map the
    run starts from. -/
theorem relative_key_inputs_are_valid :
  let tmp0 := [([Z_to_bv 8 102], [Z_to_bv 8 105])] ;
  valid_input (image_input_tmp [(devnull_relative_key, [Z_to_bv 8 104])] tmp0)
  ∧ valid_input (image_input_tmp [(localtime_relative_key, [Z_to_bv 8 104])] tmp0)
  ∧ valid_input (image_input_tmp [(urandom_relative_key, [Z_to_bv 8 104])] tmp0) := by
  dsimp only [image_input_tmp, image_input]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp [valid_argv, total_arg_bytes]
    · simp [valid_envp, total_arg_bytes]
    · unfold valid_fs
      decide
    · intro pf hpf
      simp only [List.mem_singleton] at hpf
      subst hpf
      show (100 : byte) ≠ path_slash_byte
      decide
    · dsimp only [valid_creds, valid_id, demo_uid, demo_gid]
      decide
    · dsimp only [valid_nofile, default_nofile]
      decide
    · dsimp only [valid_sigmask]
      decide
    · dsimp only [valid_hwcap, demo_hwcap]
      decide
    · exact default_urandom_infinite
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp [valid_argv, total_arg_bytes]
    · simp [valid_envp, total_arg_bytes]
    · unfold valid_fs
      decide
    · intro pf hpf
      simp only [List.mem_singleton] at hpf
      subst hpf
      show (101 : byte) ≠ path_slash_byte
      decide
    · dsimp only [valid_creds, valid_id, demo_uid, demo_gid]
      decide
    · dsimp only [valid_nofile, default_nofile]
      decide
    · dsimp only [valid_sigmask]
      decide
    · dsimp only [valid_hwcap, demo_hwcap]
      decide
    · exact default_urandom_infinite
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp [valid_argv, total_arg_bytes]
    · simp [valid_envp, total_arg_bytes]
    · unfold valid_fs
      decide
    · intro pf hpf
      simp only [List.mem_singleton] at hpf
      subst hpf
      show (100 : byte) ≠ path_slash_byte
      decide
    · dsimp only [valid_creds, valid_id, demo_uid, demo_gid]
      decide
    · dsimp only [valid_nofile, default_nofile]
      decide
    · dsimp only [valid_sigmask]
      decide
    · dsimp only [valid_hwcap, demo_hwcap]
      decide
    · exact default_urandom_infinite

/-! And on those admitted images the three opens are ANSWERED: the
    seeded "/tmp/f" key did not trip a guard, and neither did the
    relative key that spells the device's own name without its leading
    separator.  /dev/null mints [State.FdDevNull], /dev/urandom mints
    [State.FdUrandom], /etc/localtime is the -ENOENT its declaration
    promises. -/
theorem device_opens_answer_on_a_valid_image :
  let tmp0 : Fs.Fs := [([Z_to_bv 8 102], [Z_to_bv 8 105])] ;
  let opn key bs n eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff)
        (init_model [] 0 0 demo_sp demo_limit
           (image_input_tmp [(key, [Z_to_bv 8 104])] tmp0)) ;
  ((match opn devnull_relative_key devnull_bytes 10 (mkEffect 3 [] []) with
   | check_result.CheckOk m [] => fd_lookup (m_fds m) 3 = some (FdEntry.FdDevNull true false)
   | _ => False
   ))
  ∧ ((match opn urandom_relative_key urandom_bytes 13 (mkEffect 3 [] []) with
      | check_result.CheckOk m [] => fd_lookup (m_fds m) 3 = some FdEntry.FdUrandom
      | _ => False
      ))
  ∧ ((match opn localtime_relative_key localtime_bytes 15
              (mkEffect (errno_ret ENOENT) [] []) with
      | check_result.CheckOk _ [] => True
      | _ => False
      ))
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A table with the device at 3, over the declared stream. -/
def urandom_model : Model :=
  with_urandom (urandom_stream urandom_decl)
    (mkModel [(0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
              (3, FdEntry.FdUrandom)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [])

/-! 128 writable bytes at 4096, the destination of every read below. -/
def urandom_wmem : word → Option byte :=
  fun a => if (zleb 4096 (bv_unsigned a) && zltb (bv_unsigned a) 4224)
           then some (Z_to_bv 8 0) else none

/-! THE COMMON SHAPE: open, read, close.  A read of eight bytes
    delivers exactly the first eight of the declaration and advances
    the stream past them; the next read of eight delivers the next
    eight; a claimed delivery of other bytes, a short one, or one
    into another buffer is rejected; a zero count is 0 and consumes
    nothing; an unmapped destination is -EFAULT and consumes nothing;
    a write through the descriptor is -EBADF; close returns the
    model to its opening state. -/
theorem urandom_open_read_close :
  let call no args eff m := check_syscall
        (SyscallInput.mkInput no args (fun _ => none) urandom_wmem) eff m ;
  let first8 := List.map (fun z => Z_to_bv 8 z) (List.take 8 urandom_decl) ;
  let next8 := List.map (fun z => Z_to_bv 8 z) (List.take 8 (List.drop 8 urandom_decl)) ;
  (match check_syscall
          (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
             (open_path_mem urandom_bytes) (fun _ => none))
          (with_copyins [(8192, 13)] (mkEffect 3 [] [])) urandom_m0 with
  | check_result.CheckOk m1 [] =>
      ((match call 63 [3, 4096, 8, 0, 0, 0] (mkEffect 8 [(4096, first8)] []) m1 with
       | check_result.CheckOk m2 [] =>
           m_urandom m2 = urandom_stream (List.drop 8 urandom_decl)
           ∧ ((match call 63 [3, 4096, 8, 0, 0, 0] (mkEffect 8 [(4096, next8)] []) m2 with
               | check_result.CheckOk m3 [] => m_urandom m3 = IEof
                                  ∧ call 63 [3, 4096, 1, 0, 0, 0] (mkEffect 0 [] []) m3
                                     = check_result.CheckUnmodeled
               | _ => False ))
           ∧ call 63 [3, 4096, 8, 0, 0, 0] (mkEffect 8 [(4096, first8)] []) m2 = check_result.CheckReject
       | _ => False ))
      ∧ call 63 [3, 4096, 8, 0, 0, 0] (mkEffect 8 [(4096, next8)] []) m1 = check_result.CheckReject
      ∧ call 63 [3, 4096, 8, 0, 0, 0] (mkEffect 4 [(4096, List.take 4 first8)] []) m1
         = check_result.CheckReject
      ∧ call 63 [3, 4096, 8, 0, 0, 0] (mkEffect 8 [(4100, first8)] []) m1 = check_result.CheckReject
      ∧ call 63 [3, 4096, 0, 0, 0, 0] (mkEffect 0 [] []) m1 = check_result.CheckOk m1 []
      ∧ check_syscall (SyscallInput.mkInput 63 [3, 4096, 8, 0, 0, 0] (fun _ => none) (fun _ => none))
           (mkEffect (errno_ret EFAULT) [] []) m1 = check_result.CheckOk m1 []
      ∧ call 64 [3, 4096, 8, 0, 0, 0] (mkEffect (errno_ret EBADF) [] []) m1 = check_result.CheckOk m1 []
      ∧ call 57 [3, 0, 0, 0, 0, 0] (mkEffect 0 [] []) m1 = check_result.CheckOk urandom_m0 []
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE STREAM RUNNING OUT IS A DECLINE, not a short read: a
    declaration of four bytes cannot meet a request for eight, and a
    claimed short delivery is not accepted either.

    THE DECLINE IS UNREACHABLE UNDER [Run.valid_input], and that is why
    it is pinned here rather than deleted.  [Run.valid_urandom] asks
    that a launch's declared stream never end, so no valid input reaches
    this row.  The arm is still TOTAL over [State.InputStream] — it has
    to be, the type admits [State.IEof] — and a caller outside
    [Run.valid_input] still meets the decline, which is what the model
    literals below are.  What they record is the exact shape the
    validity clause excludes, so that deleting the clause would show up
    as a whole-program theorem going false rather than as a pin quietly
    becoming reachable.
    [Checks.Examples.the_random_clause_is_what_the_fixture_carries] is
    the input side of the same fact.

    THE LAST CONJUNCT KEEPS THE FIRST THREE HONEST: the stream every
    valid input declares ([State.default_urandom]) delivers EVERY count
    in full, so the test the first three conjuncts fail —
    [Sys.Fs.ReadWrite.read_urandom]'s comparison of the delivered length
    against [State.rw_count_clamp count] — is one it passes at every
    count at once.  So the decline is about the DECLARATION's length and
    not about the device.  It is stated over the take rather than over a
    [check_syscall] literal because a model holding
    [State.default_urandom] holds a [CoFixpoint], which no [vm_compute]
    may be handed; [State.stream_take_z_infinite_length] is the fact
    the arm actually reads. -/
theorem urandom_stream_runs_out :
  let m := with_urandom (urandom_stream [1, 2, 3, 4]) urandom_model ;
  let call eff := check_syscall
        (SyscallInput.mkInput 63 [3, 4096, 8, 0, 0, 0] (fun _ => none) urandom_wmem) eff m ;
  call (mkEffect 4 [(4096, List.map (fun z => Z_to_bv 8 z) [1, 2, 3, 4])] []) = check_result.CheckUnmodeled
  ∧ call (mkEffect 8 [(4096, List.map (fun z => Z_to_bv 8 z) [1, 2, 3, 4, 0, 0, 0, 0])] [])
     = check_result.CheckUnmodeled
  ∧ ((match check_syscall
              (SyscallInput.mkInput 63 [3, 4096, 4, 0, 0, 0] (fun _ => none) urandom_wmem)
              (mkEffect 4 [(4096, List.map (fun z => Z_to_bv 8 z) [1, 2, 3, 4])] []) m with
      | check_result.CheckOk m' [] => m_urandom m' = IEof | _ => False ))
  ∧ (∀ n, (0 ≤ n) →
        Int.ofNat ((Prod.fst (stream_take_z default_urandom n)).length) = n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro n Hn
    exact stream_take_z_infinite_length default_urandom n default_urandom_infinite Hn

/-! THE DISPATCH SITES.  [lseek] is 0 for every whence and offset
    ([noop_llseek] over the pinned position) and a claimed
    repositioning is rejected; [pread64] at any position delivers the
    front of the stream exactly as [read] does; [pwrite64] and
    [writev] are -EBADF; [fsync] and [ftruncate] are -EINVAL;
    [getdents64] is -ENOTDIR; [dup] copies the entry; [fcntl] F_SETFD
    is 0 and F_GETFL declines; [ioctl] RNDGETENTCNT and [flock] fail
    closed; [fstat] into an unbacked destination declines, and its
    delivering example follows. -/
theorem urandom_dispatch_sites :
  let call no args eff := check_syscall
        (SyscallInput.mkInput no args (fun _ => none) urandom_wmem) eff urandom_model ;
  let first8 := List.map (fun z => Z_to_bv 8 z) (List.take 8 urandom_decl) ;
  call 62 [3, 3, 0, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk urandom_model []
  ∧ call 62 [3, 3, 0, 0, 0, 0] (mkEffect 3 [] []) = check_result.CheckReject
  ∧ call 62 [3, 7, 2, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk urandom_model []   /- SEEK_END -/
  ∧ call 62 [3, 0, 4, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk urandom_model []   /- SEEK_HOLE -/
  ∧ ((match call 67 [3, 4096, 8, 100, 0, 0] (mkEffect 8 [(4096, first8)] []) with
      | check_result.CheckOk m [] => m_urandom m = urandom_stream (List.drop 8 urandom_decl)
      | _ => False ))
  ∧ call 68 [3, 4096, 5, 100, 0, 0] (mkEffect (errno_ret EBADF) [] []) = check_result.CheckOk urandom_model []
  ∧ call 82 [3, 0, 0, 0, 0, 0] (mkEffect (errno_ret EINVAL) [] []) = check_result.CheckOk urandom_model []
  ∧ call 46 [3, 0, 0, 0, 0, 0] (mkEffect (errno_ret EINVAL) [] []) = check_result.CheckOk urandom_model []
  ∧ call 61 [3, 4096, 1024, 0, 0, 0] (mkEffect (errno_ret ENOTDIR) [] [])
     = check_result.CheckOk urandom_model []
  ∧ ((match call 23 [3, 0, 0, 0, 0, 0] (mkEffect 4 [] []) with
      | check_result.CheckOk m [] => fd_lookup (m_fds m) 4 = some FdEntry.FdUrandom
      | _ => False ))
  ∧ call 25 [3, F_SETFD, 1, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckOk urandom_model []
  ∧ call 25 [3, F_GETFL, 0, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 80 [3, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) urandom_model = check_result.CheckUnmodeled
  ∧ call 29 [3, TCGETS, 4096, 0, 0, 0] (mkEffect (errno_ret ENOTTY) [] [])
     = check_result.CheckUnmodeled
  ∧ call 32 [3, 2, 0, 0, 0, 0] (mkEffect 0 [] []) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! fstat ON /dev/urandom ASSERTS THE RANDOM DEVICE: S_IFCHR with
    [st_rdev] 1:9 and a zero size is accepted and PINNED under
    [urandom_path]; the null device's number, a regular file, and a
    nonzero size are rejected; a second fstat must repeat the pin's
    stable members. -/
theorem urandom_fstat_asserts_the_device :
  let call m eff := check_syscall
        (SyscallInput.mkInput 80 [3, 4096, 0, 0, 0, 0] (fun _ => none) urandom_wmem) eff m ;
  let good := dev_stat S_IFCHR URANDOM_RDEV 0 ;
  let deliver bs := mkEffect 0 [(4096, bs)] [] ;
  ((match call urandom_model (deliver good) with
   | check_result.CheckOk m [] =>
       statpin_lookup (m_statpins m) urandom_path = some good
       ∧ call m (deliver good) = check_result.CheckOk m []
       ∧ call m (deliver (Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 7
                            ++ List.drop 16 good)) = check_result.CheckReject
   | _ => False
   ))
  ∧ call urandom_model (deliver (dev_stat S_IFCHR DEVNULL_RDEV 0)) = check_result.CheckReject
  ∧ call urandom_model (deliver (dev_stat S_IFREG 0 5)) = check_result.CheckReject
  ∧ call urandom_model (deliver (dev_stat S_IFCHR URANDOM_RDEV 5)) = check_result.CheckReject
  ∧ call urandom_model (mkEffect 0 [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE SAME STREAM ON BOTH SIDES OF A PAIR.  A source and a target
    that differ in everything the model lets them differ in — here the
    descriptor table, so the device sits at 3 on one side and at 5 on
    the other — read the same eight bytes when they are seeded from one
    [in_urandom], and are left holding the same remainder.  Concretely
    below; in general [Checks.Sys.Fs.ReadWrite.check_read_urandom_same_stream],
    which this instantiates. -/
theorem urandom_same_bytes_on_both_sides :
  let inp := ProcInput.mkProcInput_full [[]] [] [] IEof
               demo_uid demo_gid demo_groups net_silent
               default_nofile (Z_to_bv 64 0) demo_hwcap false .Sv48
               (urandom_stream urandom_decl) [] ;
  let src := with_fds (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit inp))
                         3 FdEntry.FdUrandom)
               (init_model [] 0 0 demo_sp demo_limit inp) ;
  let tgt := with_fds (fd_insert (fd_insert (m_fds (init_model [] 0 0 demo_sp demo_limit inp))
                                    4 FdEntry.FdDir) 5 FdEntry.FdUrandom)
               (init_model [] 0 0 demo_sp demo_limit inp) ;
  let first8 := List.map (fun z => Z_to_bv 8 z) (List.take 8 urandom_decl) ;
  let read fd m eff := check_syscall
        (SyscallInput.mkInput 63 [fd, 4096, 8, 0, 0, 0] (fun _ => none) urandom_wmem) eff m ;
  (match read 3 src (mkEffect 8 [(4096, first8)] []),
        read 5 tgt (mkEffect 8 [(4096, first8)] []) with
  | check_result.CheckOk s' [], check_result.CheckOk t' [] =>
      m_urandom s' = m_urandom t'
      ∧ m_urandom s' = urandom_stream (List.drop 8 urandom_decl)
  | _, _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

theorem urandom_same_bytes_in_general :
  ∀ i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2,
  m_urandom m1 = m_urandom m2 →
  check_read_urandom i buf count eff1 m1 = check_result.CheckOk m1' evs1 →
  check_read_urandom i buf count eff2 m2 = check_result.CheckOk m2' evs2 →
  eff_writes eff1 = eff_writes eff2 ∧ m_urandom m1' = m_urandom m2' := by
  intro i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2 Hu H1 H2
  obtain ⟨Hw, _, Hm⟩ :=
    check_read_urandom_same_stream i buf count eff1 eff2 m1 m2 m1' m2' evs1 evs2 Hu H1 H2
  exact ⟨Hw, Hm⟩

/-! ".." AND "." GET THE SAME ANSWER ON EVERY ARM, which is a claim
    about two flag words and two pathnames at once and so is a literal
    rather than a real run: a run makes the one call it makes.  Both are
    directory references the walk answers without a lookup, so the
    clobbering shape is -EISDIR for each and the read shape hands back a
    directory fd for each.

    Without this arm, the second of each pair would be wrong: the
    create shape would MINT A KEY SPELLED "..", and the read shape would
    answer -ENOENT, which Linux never returns for "..".  The last conjunct is
    the control that keeps the first four from being satisfied by a
    model that declines everything — a claimed SUCCESS on the create
    shape is rejected, for ".." exactly as for ".". -/
theorem openat_dotdot_answers_as_dot_does :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let opn bs n fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  let dot := [46] ; let dotdot := [46, 46] ;
  /- the clobbering shape: -EISDIR for both, and it really is an Ok -/
  opn dot 2 wr_create_flags (mkEffect (errno_ret EISDIR) [] [])
    = check_result.CheckOk m0 []
  ∧ opn dotdot 3 wr_create_flags (mkEffect (errno_ret EISDIR) [] [])
     = check_result.CheckOk m0 []
  /- the read shape: a directory fd at the lowest free slot, for both -/
  ∧ (match opn dot 2 0 (mkEffect 3 [] []) with
     | check_result.CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = some FdEntry.FdDir
     | _ => False )
  ∧ (match opn dotdot 3 0 (mkEffect 3 [] []) with
     | check_result.CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = some FdEntry.FdDir
     | _ => False )
  /- ...and neither is answered by declining: a claimed success on the
     create shape is REFUSED, which is what makes the four above real -/
  ∧ opn dot 2 wr_create_flags (mkEffect 3 [] []) = check_result.CheckReject
  ∧ opn dotdot 3 wr_create_flags (mkEffect 3 [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE OVER-MATCH GUARD FOR [path_is_dirref], and the most load-bearing
    of the three below.  "..." is an ORDINARY NAME: it is not a directory
    reference, so the create arm mints a key for it exactly as it would
    for "f".  [path_is_dirref] uses [path_eqb] against the two constants
    and nothing else, so this holds — but nothing else in the tree
    pins it, and the obvious "improvement" of matching a LEADING ".."
    would break it silently, turning every dotfile-ish name into a
    directory reference.  A real run cannot make this claim: it would show
    one open succeeding, not that the classifier draws its line between
    ".." and "...".

    The three-byte path also sits one byte past [dotdot_path], which is
    where a prefix test rather than an equality test would go wrong. -/
theorem openat_dot3_is_an_ordinary_name :
  (match check_syscall
          (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
             (open_path_mem [46, 46, 46]) (fun _ => none))
          (with_copyins [(8192, 4)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) with
  | check_result.CheckOk m [] => m_fs m = [([Z_to_bv 8 46, Z_to_bv 8 46, Z_to_bv 8 46], [])]
  | _ => False
  )
:= by rfl

/-! THE EMPTY PATHNAME BEATS O_CREAT, and no key spelled "" can ever be
    minted.  Two halves of one boundary, which is the shape a boundary
    claim needs: the deterministic -ENOENT is accepted with the model
    unchanged, and a kernel claiming the create SUCCEEDED is refused.
    [openat_body_spec] answers the empty path before it reaches any arm,
    so this is a statement about the ORDER of two tests rather than about
    either one, and a spec that let O_CREAT run first would mint a key
    under the empty name and still pass every other case in this file. -/
theorem openat_empty_path_beats_o_creat :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let opn eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
           (open_path_mem []) (fun _ => none))
        (with_copyins [(8192, 1)] eff) m0 ;
  opn (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckOk m0 []
  ∧ opn (mkEffect 3 [] []) = check_result.CheckReject
:= by constructor <;> rfl

/- ================================ openat's O_DIRECTORY arm

   [Fs.Open.openat_dir_spec] answers O_RDONLY|O_DIRECTORY.  Three claims
   about it that a real run cannot make: an equality between two FLAG
   WORDS, a decline that must not depend on what the kernel said, and a
   file-system image whose keys hold a separator — no modeled syscall
   puts one there. -/

/-! THE ARM'S FOUR ANSWERS, AND THE FLAG IS REALLY READ.  The last two
    conjuncts are what make the first four evidence of anything: a
    claimed SUCCESS on a name the map holds is refused, so the -ENOTDIR
    is not a spec that admits everything; and the SAME name under bare
    O_RDONLY is a readable file fd rather than -ENOTDIR, so the errno is
    O_DIRECTORY's doing and not the name's.  A real run issues one flag
    word per call and cannot state either. -/
theorem openat_directory_answers :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let opn fs bs n fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 0, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) (m0 fs) ;
  let dir_word := (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC) ;
  let hfs : Fs.Fs := [([Z_to_bv 8 97], [104])] ;
  /- "." and "..": a directory fd at the lowest free slot, the same
     [FdDir] the plain read arm hands back -/
  ((match opn [] [46] 2 dir_word (mkEffect 3 [] []) with
   | check_result.CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = some FdEntry.FdDir
   | _ => False ))
  ∧ ((match opn [] [46, 46] 3 dir_word (mkEffect 3 [] []) with
      | check_result.CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3) = some FdEntry.FdDir
      | _ => False ))
  /- a name the map holds is not a directory: -ENOTDIR, model unchanged -/
  ∧ opn hfs [97] 2 dir_word (mkEffect (errno_ret ENOTDIR) [] [])
     = check_result.CheckOk (m0 hfs) []
  /- an absent name never reaches the directory test: -ENOENT -/
  ∧ opn [] [97] 2 dir_word (mkEffect (errno_ret ENOENT) [] [])
     = check_result.CheckOk (m0 []) []
  /- ...and a claimed descriptor for the name the map holds is REFUSED -/
  ∧ opn hfs [97] 2 dir_word (mkEffect 3 [] []) = check_result.CheckReject
  /- ...while the same name under bare O_RDONLY is a file fd, so the
     -ENOTDIR above is the flag's answer and not the name's -/
  ∧ ((match opn hfs [97] 2 0 (mkEffect 3 [] []) with
      | check_result.CheckOk m [] => fd_lookup (m_fds m) (Z_to_bv 64 3)
                        = some (FdEntry.FdFile [Z_to_bv 8 97] (Z_to_bv 64 0))
      | _ => False ))
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE IGNORED BITS ARE IGNORED HERE TOO, which is an EQUALITY BETWEEN
    TWO FLAG WORDS and so cannot be a real run: a run issues one word,
    and could show the four-bit word conforming without showing
    that it lands where the two-bit word lands.  Stated over all four of
    the arm's answers at once, since a mask applied in one branch and
    not another is exactly the mistake this catches. -/
theorem openat_directory_ignores_largefile_and_cloexec :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let opn fs bs n fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 0, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) (m0 fs) ;
  let wide := (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC) ;
  let hfs : Fs.Fs := [([Z_to_bv 8 97], [104])] ;
  opn [] [46] 2 wide (mkEffect 3 [] [])
    = opn [] [46] 2 O_DIRECTORY (mkEffect 3 [] [])
  ∧ opn [] [46, 46] 3 wide (mkEffect 3 [] [])
     = opn [] [46, 46] 3 O_DIRECTORY (mkEffect 3 [] [])
  ∧ opn hfs [97] 2 wide (mkEffect (errno_ret ENOTDIR) [] [])
     = opn hfs [97] 2 O_DIRECTORY (mkEffect (errno_ret ENOTDIR) [] [])
  ∧ opn [] [97] 2 wide (mkEffect (errno_ret ENOENT) [] [])
     = opn [] [97] 2 O_DIRECTORY (mkEffect (errno_ret ENOENT) [] [])
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE IMPLIED-DIRECTORY DECLINE, and the half no real run reaches: the
    claim is over two kernel answers that could not both be right.  A
    key "a/b" means reality has a directory "a", so Linux hands back a
    directory fd where the map would answer -ENOENT — and the arm
    declines whichever of the two the kernel is offered as having given,
    so it is not quietly agreeing with one of them.

    The control is the same call on the same NAME with nothing under it,
    which IS answered.  Without it a decline here would be satisfied
    just as well by an arm that declines every ordinary name.

    This guard is on the O_DIRECTORY arm and not on the read arm, and
    the asymmetry is deliberate: [Fs.Open.openat_dir_spec] records why
    this one can take it.  The write-create
    arms neither guard nor mint: they ANSWER the implied directory
    ([openat_implied_directory_create_eisdir] above). -/
theorem openat_directory_implied_directory_unmodeled :
  let m0 fs := init_model [] 0 0 demo_sp demo_limit (demo_input fs IEof) ;
  let opn fs eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192,
                     Z_to_bv 64 (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC),
                     0, 0, 0]
           (open_path_mem [97]) (fun _ => none))
        (with_copyins [(8192, 2)] eff) (m0 fs) ;
  let under : Fs.Fs := [([Z_to_bv 8 97, Z_to_bv 8 47, Z_to_bv 8 98], [104])] ;
  opn under (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn under (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckUnmodeled
  ∧ opn [] (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckOk (m0 []) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE NAME_MAX BOUNDARY, stated as the pair a boundary claim needs: a
    256-byte component is declined and a 255-byte one is answered.  Over
    [Uapi.NAME_MAX] the -ENAMETOOLONG belongs to the FILESYSTEM
    ([ext4_lookup]'s EXT4_NAME_LEN test, [simple_lookup]'s NAME_MAX
    test), and a model with no filesystem type would be inventing one;
    a real run cannot make the claim, because the kernel it runs on has a
    filesystem and simply answers. -/
theorem openat_directory_name_max_boundary :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let opn bs n eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192,
                     Z_to_bv 64 (O_DIRECTORY + O_LARGEFILE + O_CLOEXEC),
                     0, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  opn (List.replicate 256 97) 257 (mkEffect (errno_ret ENOENT) [] [])
    = check_result.CheckUnmodeled
  ∧ opn (List.replicate 255 97) 256 (mkEffect (errno_ret ENOENT) [] [])
     = check_result.CheckOk m0 []
:= by constructor <;> rfl

/- ================================================ faccessat2 (439)

   Four claims, over the one thing faccessat2 adds to faccessat: the flag
   word.  A real run cannot make these four claims: it cannot run TWO
   flag words against one another (it gets the answer for the word it
   passed), vary the kernel's answer under a decline, or build a
   file-system image whose keys hold a separator. -/

/-! The model both faccessat2 examples below run against: one present
    key "a", nothing else. -/
def fa2_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof)

/-! ACCEPTED FLAGS CHANGE NO ANSWER, which is the sharpest claim
    [Fs.Open.faccessat2_spec] makes and the one no real run reaches: it is
    an EQUALITY BETWEEN FLAG WORDS, and a run is shown the answer for the
    word it passed.  The same call under 0, AT_EACCESS,
    AT_SYMLINK_NOFOLLOW and both lands in exactly the same place —
    accepted, model untouched, no events — because under F_OK neither bit
    reaches anything the model holds: AT_EACCESS only picks which cred
    the walk runs under, and every DAC comparison narrows a zero mask
    away first; AT_SYMLINK_NOFOLLOW only stops a trailing symlink being
    followed, and a resolvable key here is a regular file. -/
theorem faccessat2_accepted_flags_change_no_answer :
  let call flags := check_syscall
        (SyscallInput.mkInput 439 [AT_FDCWD, 8192, 0, Z_to_bv 64 flags, 0, 0] fa_mem_name_a
           (fun _ => none))
        (with_copyins [(8192, 2)] (mkEffect 0 [] []))
        fa2_model ;
  call 0 = check_result.CheckOk fa2_model []
  ∧ call AT_EACCESS = check_result.CheckOk fa2_model []
  ∧ call AT_SYMLINK_NOFOLLOW = check_result.CheckOk fa2_model []
  ∧ call (zlor AT_EACCESS AT_SYMLINK_NOFOLLOW) = check_result.CheckOk fa2_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! AT_EMPTY_PATH IS DECLINED, AND THE DECLINE DOES NOT DEPEND ON WHAT
    THE KERNEL SAID — the half no real run reaches, since a run is shown
    one answer and the claim here is over two that could not both be
    right.  The kernel really answers 0 (LOOKUP_EMPTY makes the dirfd
    itself the target, so an empty pathname becomes the working
    directory and a nonempty one resolves as usual), and the model
    declines whichever answer is offered rather than quietly agreeing
    with one.  The pathname here is present and resolvable, so nothing
    but the flag can be what the decline is about. -/
theorem faccessat2_empty_path_flag_declined_either_way :
  let call eff := check_syscall
        (SyscallInput.mkInput 439 [AT_FDCWD, 8192, 0, Z_to_bv 64 AT_EMPTY_PATH, 0, 0]
           fa_mem_name_a (fun _ => none))
        (with_copyins [(8192, 2)] eff)
        fa2_model ;
  call (mkEffect 0 [] []) = check_result.CheckUnmodeled
  ∧ call (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckUnmodeled
:= by constructor <;> rfl

/-! THE FLAG -EINVAL READS NO USER MEMORY, for the reason the mode
    -EINVAL does not: [do_faccessat] tests the flag word in its SECOND
    statement, before [user_path_at] is called, so a ledger claimed on
    that arm is a read Linux did not perform.  This is the case a spec
    that wrapped the whole body in [record_copyins] gets wrong.
    AT_SYMLINK_FOLLOW (0x400) is a real AT_ constant OUTSIDE the three
    faccessat2 accepts, so the -EINVAL is the kernel's own answer and
    not a decline; the pair differs in the ledger alone. -/
theorem faccessat2_bad_flag_records_no_copyin :
  let call eff := check_syscall
        (SyscallInput.mkInput 439 [AT_FDCWD, 8192, 0, Z_to_bv 64 1024, 0, 0] fa_mem_name_a
           (fun _ => none))
        eff fa2_model ;
  call (mkEffect (errno_ret EINVAL) [] []) = check_result.CheckOk fa2_model []
  ∧ call (with_copyins [(8192, 2)] (mkEffect (errno_ret EINVAL) [] []))
     = check_result.CheckReject
:= by constructor <;> rfl

/-! The implied-directory decline reaches the 439 arm too, and it is the
    one faccessat decline only the starting image can set up: a key living
    UNDER a name means reality has a DIRECTORY the flat map only
    implies, and F_OK of a directory is 0 where the map would answer
    -ENOENT.  Stated again here because [Fs.Open.faccessat2_spec] is a
    separate arm — sharing [Fs.Open.faccessat_body_spec] is what makes
    it hold, and this is what says the sharing survived. -/
theorem faccessat2_implied_directory_unmodeled :
  check_syscall
    (SyscallInput.mkInput 439 [AT_FDCWD, 8192, 0, Z_to_bv 64 AT_EACCESS, 0, 0]
       fa_mem_name_a (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []), ([97, 47, 98], [104])] IEof))
  = check_result.CheckUnmodeled
:= by rfl

/- ============================== "/tmp/<one component>", the answered family

   [Fs.Open.openat_tmp_spec] answers two flag words for a path of the
   shape "/tmp/<one component>", over the run's declared private /tmp
   ([State.in_tmp], seeded under absolute keys by [State.fs_seed_tmp]).
   The premise it rests on — /tmp is writable and PRIVATE to this run —
   is an assumption of the model, stated on the arm. -/

/-! The bytes of "/tmp/out.gif". -/
def tmp_gif_bytes : List Int :=
  [47, 116, 109, 112, 47, 111, 117, 116, 46, 103, 105, 102]

/-! The same path as a model KEY, which is what the seeding produces and
    what the arms look up. -/
def tmp_gif_key : Fs.path :=
  List.map (fun z => Z_to_bv 8 z) tmp_gif_bytes

/-! THE ROUND TRIP, on a run whose declared /tmp is EMPTY: create the
    name, then read it back at a second descriptor, then remove it.
    This is the shape a program makes when it writes a temporary file,
    reads it back and removes it.  The create records the key EMPTY,
    exactly as [Fs.Open.create_wronly] does; the descriptor is an
    ordinary [State.FdFileW] on the absolute key, so nothing later in the
    run needs an arm of its own. -/
theorem openat_tmp_create_read_unlink :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let opn fl eff m := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem tmp_gif_bytes) (fun _ => none))
        (with_copyins [(8192, 13)] eff) m ;
  (match opn wr_create_flags (mkEffect 3 [] []) m0 with
  | check_result.CheckOk m1 [] =>
      /- the key is there, empty, and the descriptor is write-only on it -/
      m_fs m1 = [(tmp_gif_key, [])]
      ∧ fd_lookup (m_fds m1) (Z_to_bv 64 3) = some (FdEntry.FdFileW tmp_gif_key (Z_to_bv 64 0))
      /- the read shape now answers, at the next free descriptor -/
      ∧ (match opn 0 (mkEffect 4 [] []) m1 with
         | check_result.CheckOk m2 [] =>
             fd_lookup (m_fds m2) (Z_to_bv 64 4) = some (FdEntry.FdFile tmp_gif_key (Z_to_bv 64 0))
         | _ => False )
      /- ...and the removal takes the key away, once no fd names it -/
      ∧ (match check_syscall
                 (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0]
                    (open_path_mem tmp_gif_bytes) (fun _ => none))
                 (with_copyins [(8192, 13)] (mkEffect 0 [] []))
                 (with_fds [] m1) with
         | check_result.CheckOk m3 [] => m_fs m3 = []
         | _ => False )
      /- THE IGNORED BITS COME THROUGH.  The word is matched past
         [Open.open_ignored_flags] — O_CLOEXEC, O_LARGEFILE and
         O_NONBLOCK, the file's shared mask — not past O_CLOEXEC alone,
         so the create word carrying any of them reaches the same arm
         and records the same key.  A real run cannot separate this
         from the bare word; only a literal can. -/
      ∧ opn (wr_create_flags + O_CLOEXEC) (mkEffect 3 [] []) m0
         = check_result.CheckOk m1 []
      ∧ opn (wr_create_flags + O_NONBLOCK) (mkEffect 3 [] []) m0
         = check_result.CheckOk m1 []
      ∧ opn (wr_create_flags + O_LARGEFILE) (mkEffect 3 [] []) m0
         = check_result.CheckOk m1 []
      /- ...and so does the read word -/
      ∧ (match opn (0 + O_CLOEXEC) (mkEffect 4 [] []) m1 with
         | check_result.CheckOk m2 [] =>
             fd_lookup (m_fds m2) (Z_to_bv 64 4)
               = some (FdEntry.FdFile tmp_gif_key (Z_to_bv 64 0))
         | _ => False )
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A read of a name the ENVIRONMENT declared rather than the run
    created.  The declaration is keyed by the one component ("out.gif")
    and the program names the whole path; [State.fs_seed_tmp] is what
    makes those the same file, and this is the case that says so. -/
theorem openat_tmp_declared_name_reads :
  (match check_syscall
          (SyscallInput.mkInput 56 [AT_FDCWD, 8192, 0, 420, 0, 0]
             (open_path_mem tmp_gif_bytes) (fun _ => none))
          (with_copyins [(8192, 13)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp [] [([111, 117, 116, 46, 103, 105, 102], [104, 105])] IEof)) with
  | check_result.CheckOk m [] =>
      fd_lookup (m_fds m) (Z_to_bv 64 3) = some (FdEntry.FdFile tmp_gif_key (Z_to_bv 64 0))
      ∧ Fs.fs_lookup (m_fs m) tmp_gif_key = some [104, 105]
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE DECLARATION NEEDS NO VALIDITY CLAUSE, which is the point of
    seeding it one entry at a time through [Fs.fs_set]: an unsorted
    declaration with a repeat in it still seeds the canonical form, and
    the later entry wins.  [State.fs_seed_tmp_valid] is the general
    statement; this is it on a literal the [Fs.valid_fs] of an image
    would have refused outright. -/
theorem openat_tmp_unsorted_declaration_is_canonical :
  let fs := m_fs (init_model [] 0 0 demo_sp demo_limit
                    (demo_input_tmp []
                       [([98], [1]), ([97], [2]), ([98], [3])] IEof)) ;
  /- the canonical form, out of a declaration that was not in it -/
  Fs.fs_sorted fs = true
  ∧ fs.length = 2
  /- each declared name under its absolute key, the later "b" winning -/
  ∧ Fs.fs_lookup fs (tmp_key [97]) = some [2]
  ∧ Fs.fs_lookup fs (tmp_key [98]) = some [3]
  /- AND THE COLLISION: an IMAGE that already holds the absolute key,
     beside a declaration that names the component, resolves to the
     DECLARATION's bytes.  [Fs.valid_fs] admits such an image — its keys
     are only sorted and NUL-free, and nothing forbids one beginning
     "/tmp/" — and the seeding's [Fs.fs_set] replaces rather than
     appends, so the run holds one file at that name and it is the
     declared one.  Which way the collision falls is a choice; this is
     where it is written down. -/
  ∧ Fs.fs_lookup
       (m_fs (init_model [] 0 0 demo_sp demo_limit
                (demo_input_tmp [(tmp_gif_key, [1])]
                   [([111, 117, 116, 46, 103, 105, 102], [2])] IEof)))
       tmp_gif_key = some [2]
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! WHAT STAYS DECLINED, each on a model that HOLDS the key, so that
    none of them is declining for want of the file.  A read of a name
    the run does NOT hold is the one decline the privacy premise could
    have answered -ENOENT; the model declines it, and it is stated on
    the empty model beside the rest. -/
theorem openat_tmp_excluded_shapes_unmodeled :
  let held := init_model [] 0 0 demo_sp demo_limit
                (demo_input_tmp [] [([111, 117, 116, 46, 103, 105, 102], [104])] IEof) ;
  let empty := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let opn bs n fl eff m := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) m ;
  /- a read of a name the run does not hold -/
  opn tmp_gif_bytes 13 0 (mkEffect (errno_ret ENOENT) [] []) empty
    = check_result.CheckUnmodeled
  /- the flag words the arm leaves out, at a name that IS held -/
  ∧ opn tmp_gif_bytes 13 (O_RDWR + O_CREAT + O_TRUNC)
       (mkEffect 3 [] []) held = check_result.CheckUnmodeled
  ∧ opn tmp_gif_bytes 13 append_create_flags (mkEffect 3 [] []) held
     = check_result.CheckUnmodeled
  ∧ opn tmp_gif_bytes 13 excl_create_flags
       (mkEffect (errno_ret EEXIST) [] []) held = check_result.CheckUnmodeled
  ∧ opn tmp_gif_bytes 13 O_DIRECTORY
       (mkEffect (errno_ret ENOTDIR) [] []) held = check_result.CheckUnmodeled
  /- a second component -/
  ∧ opn [47, 116, 109, 112, 47, 100, 47, 102] 9 wr_create_flags
       (mkEffect 3 [] []) empty = check_result.CheckUnmodeled
  /- the directory itself, and the two references inside it -/
  ∧ opn [47, 116, 109, 112] 5 0 (mkEffect 3 [] []) held
     = check_result.CheckUnmodeled
  ∧ opn [47, 116, 109, 112, 47] 6 0 (mkEffect 3 [] []) held
     = check_result.CheckUnmodeled
  ∧ opn [47, 116, 109, 112, 47, 46] 7 0 (mkEffect 3 [] []) held
     = check_result.CheckUnmodeled
  ∧ opn [47, 116, 109, 112, 47, 46, 46] 8 0 (mkEffect 3 [] []) held
     = check_result.CheckUnmodeled
  /- a name that merely BEGINS like the prefix: "/tmpfoo" is not under
     /tmp at all, and the separator decline still stands for it -/
  ∧ opn [47, 116, 109, 112, 102, 111, 111] 8 wr_create_flags
       (mkEffect 3 [] []) empty = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE [Uapi.NAME_MAX] BOUNDARY, from both sides.  The decline is this
    arm's own — the plain arms cannot afford it (see
    [Open.openat_plain_name]'s note) and this one can — so nothing else
    in the tree reaches it, and a boundary claimed on one side only is
    satisfied by an arm that declines everything.  A component of 255
    bytes is ANSWERED and a component of 256 is DECLINED, at both flag
    words the arm takes.

    The -ENAMETOOLONG a longer component really gets comes out of the
    FILESYSTEM's own lookup rather than out of fs/namei.c, so the guard
    is one-sided: it defends against a filesystem whose limit is larger
    than 255 and not against one whose limit is smaller. -/
theorem openat_tmp_name_max_boundary :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  /- "/tmp/" followed by n copies of 'a' -/
  let name n := List.replicate n 97 ;
  let opn n fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem ([47, 116, 109, 112, 47] ++ name n)) (fun _ => none))
        (with_copyins [(8192, (6 + n))] eff) m0 ;
  /- 255: answered — the create mints the key, and the read of a key the
     run does not hold is the arm's OTHER decline, not this one -/
  (match opn 255 wr_create_flags (mkEffect 3 [] []) with
  | check_result.CheckOk _ [] => True | _ => False )
  /- 256: declined, at the create word and at the read word alike -/
  ∧ opn 256 wr_create_flags (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn 256 0 (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A DIRECTORY INSIDE /tmp, which the flat map only implies: the
    declaration names "d/f", so a key lives under "/tmp/d" and
    [Fs.Namei.fs_under] sees it there.  THE CREATE WORD ANSWERS and the
    READ WORD DECLINES.

    The create word reaches [Fs.Open.openat_create_spec] — the same arm
    a working-directory name takes — so the answer is [do_open]'s
    deterministic -EISDIR (fs/namei.c, Linux v6.18.46), the model does
    not move, and the descriptor the arm would otherwise have minted is
    refused beside it.  The -ENOENT a flat map would have reached for is
    refused too, which is what separates this answer from a lookup miss.

    The read word still declines: answering means a directory
    descriptor, and the model has no directory semantics to give one. -/
theorem openat_tmp_implied_directory_create_eisdir :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100, 47, 102], [104])] IEof) ;
  let opn fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem [47, 116, 109, 112, 47, 100]) (fun _ => none))
        (with_copyins [(8192, 7)] eff) m0 ;
  opn wr_create_flags (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk m0 []
  ∧ opn wr_create_flags (mkEffect 3 [] []) = check_result.CheckReject
  ∧ opn wr_create_flags (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ...and the read word at the same name, on the same image, still
    fails closed — at the descriptor Linux would hand back and at the
    -EISDIR the create gets, so the decline is the arm's and not a
    disagreement about the errno.  The nested name "/tmp/d/f" itself is
    unchanged too: it carries a second component, which [Fs.Namei.tmp_name]
    refuses, so it is still the separator gate's decline and NOT this
    arm's. -/
theorem openat_tmp_implied_directory_read_unmodeled :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100, 47, 102], [104])] IEof) ;
  let opn bs n fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  opn [47, 116, 109, 112, 47, 100] 7 0 (mkEffect 3 [] [])
    = check_result.CheckUnmodeled
  ∧ opn [47, 116, 109, 112, 47, 100] 7 0
       (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckUnmodeled
  ∧ opn [47, 116, 109, 112, 47, 100, 47, 102] 9 0
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn [47, 116, 109, 112, 47, 100, 47, 102] 9 wr_create_flags
       (mkEffect 3 [] []) = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE READ BRANCH'S GUARD, exercised where it decides.  On the image
    above "/tmp/d" is not a key, so the read declines through the
    not-held branch whether or not [Fs.Namei.fs_under] is tested first,
    and the case above cannot tell the two orderings apart.  [Fs.valid_fs]
    admits an image holding BOTH "/tmp/d" and "/tmp/d/f" — no reality has
    both, but nothing refuses it — and there the lookup of "/tmp/d" would
    SUCCEED: without the guard the read word would mint an [FdFile] on a
    name reality makes a directory.  This is the only image on which the
    guard changes an answer, so it is the one that pins it.  The read
    still declines, at the descriptor and at the -ENOENT a lookup miss
    would have given; the create answers -EISDIR ahead of the lookup that
    would otherwise have truncated a held key, and refuses the
    descriptor.  Drop the read branch's guard and the first open below
    becomes a [CheckOk] minting fd 3; move the create's guard after the
    lookup and the -EISDIR becomes a [CheckReject]. -/
theorem openat_tmp_implied_directory_unrealizable_image :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input [([47, 116, 109, 112, 47, 100], [104]),
                           ([47, 116, 109, 112, 47, 100, 47, 102], [104])] IEof) ;
  let opn fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem [47, 116, 109, 112, 47, 100]) (fun _ => none))
        (with_copyins [(8192, 7)] eff) m0 ;
  /- the image really holds both: the name is a key AND has a key under it -/
  fs_lookup (m_fs m0) [47, 116, 109, 112, 47, 100] = some [104]
  ∧ fs_under (m_fs m0) [47, 116, 109, 112, 47, 100] = true
  /- the read declines, at the descriptor and at the lookup miss's errno -/
  ∧ opn 0 (mkEffect 3 [] []) = check_result.CheckUnmodeled
  ∧ opn 0 (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckUnmodeled
  /- the create answers -EISDIR ahead of the lookup; the descriptor is refused -/
  ∧ opn wr_create_flags (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk m0 []
  ∧ opn wr_create_flags (mkEffect 3 [] []) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE HONEST TWINS, without which the cases above are consistent
    with an arm that answers -EISDIR for everything under a /tmp holding
    a subdirectory.  The declaration is still SEEDED at its own key, so
    a name with a separator in it stays declarable — [State.in_tmp] has
    no slash-free condition — and a plain sibling name in
    the same declared /tmp still creates, since [Fs.Namei.fs_under] is a
    COMPONENT prefix and nothing lives under "/tmp/out.gif". -/
theorem openat_tmp_implied_directory_sibling_still_creates :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100, 47, 102], [104])] IEof) ;
  let opn bs n fl eff := check_syscall
        (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 fl, 420, 0, 0]
           (open_path_mem bs) (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  /- the nested declaration reaches the image at its own key -/
  fs_lookup (m_fs m0) [47, 116, 109, 112, 47, 100, 47, 102] = some [104]
  /- ...and a plain sibling in the same declared /tmp still creates -/
  ∧ (match opn tmp_gif_bytes 13 wr_create_flags (mkEffect 3 [] []) with
     | check_result.CheckOk m [] => fs_lookup (m_fs m) tmp_gif_key = some []
     | _ => False
     )
:= by constructor <;> rfl
end LinuxSem.Checks.Cases.Fs.Open
