/-
  * LinuxSem.Checks.Cases.Fs.Namei — worked examples over unlinkat (35)

  Worked cases over `Sys.Fs.Namei`, which answers to Linux [fs/namei.c]:
  the examples for the syscalls defined there, and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have are supplied as local transparent `abbrev`s below,
  DEFINITIONALLY EQUAL to what they stand for, so every statement below
  denotes exactly the same claim:
  - `Z_to_bv n z` is `BitVec.ofInt n z`, and `%nat`/`%Z` scope
    annotations are erased;
  - `repeat x n` is `List.replicate n x` (argument order swapped), so the
    `NAME_MAX` case's `List.repeat (Z_to_bv 8 97) n` becomes
    `List.replicate n (Z_to_bv 8 97)`;
  - `CheckOk`/`CheckReject`/`CheckUnmodeled` are the constructors of the
    `check_result` of `Checks.Sys.Prelude`, qualified because they live
    in its namespace;
  - `mkInput` is `SyscallInput.mkInput`;
  - a record field is read by dot notation here (`m.m_fs`), the same
    projection the prelude applies as a function;
    `m_fds`/`m_fs`/`m_stdin`/`m_pipes` are already functions
    (`StateLedger`), so they need no shim.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  `decide` cannot be the rule: `check_result` carries
  a `Model` and so has no `DecidableEq`.

  The `match`-shaped examples.  Seven examples state their claim as a
  `match` on the checker's answer rather than as an equality —
  [unlinkat_byte_prefix_is_not_a_directory], the trailing separator
  case, and the whole `/tmp` group.  Lean has no `end` terminator and
  its arms are greedy, so each is parenthesised —
  `(match … with | … )` — which denotes the same term; `False` is the
  wildcard arm's type, and an arm written without a leading `|` is given
  one, since Lean requires it.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Namei
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
open LinuxSem.LinuxProcessSem.Sys.Fs.Namei
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Namei

open LinuxSem.Common.RocqSpelling

/-! The Rocq spellings used below (`bv_unsigned`, `Z_to_bv`, …) are the shared transparent aliases of `LinuxSem.Common.RocqSpelling`. -/

/-! * LinuxProcessSem.Checks.Cases.Fs.Namei — worked examples over unlinkat (35)

    Worked cases over `Sys.Fs.Namei`, which answers to Linux [fs/namei.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/
/-! Path bytes at 8192 for the unlinkat examples below: 'a', NUL. -/
def mem_name_a : word → Option byte :=
  fun a => if bv_eqb a 8192 then some 97        /- 'a' -/
           else if bv_eqb a 8193 then some 0    /- NUL -/
           else none

/-! A key living UNDER a name means reality has a DIRECTORY that the flat
    map only implies: unlinking that name is -EISDIR on Linux and would be
    -ENOENT here, so [Fs.Namei.fs_under] declines it.  No modeled
    syscall puts a separator in a key, so only the starting image can
    set this up.

    This image holds "a/b" and NOT "a", which is the REALIZABLE shape: a
    real directory "a" containing a file "b" contributes exactly the one
    key. -/
theorem unlinkat_implied_directory_unmodeled :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret EISDIR) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97, 47, 98], [104])] IEof))
  = check_result.CheckUnmodeled

:= by rfl

/-! The same guard on the UNREALIZABLE image, where "a" and "a/b" are
    both keys — a tree that cannot exist, since "a" cannot be a regular
    file and a directory at once.  [Fs.valid_fs] admits it anyway, which
    is what [Fs.Namei.unlinkat_spec] means by the guard covering those
    images too, and this is the case that pins it: here the lookup of "a"
    would SUCCEED, so a guard placed after the lookup would remove the
    file and return 0 instead of declining.  On the realizable image
    above the lookup misses either way, so that one cannot tell the two
    orderings apart. -/
theorem unlinkat_implied_directory_unrealizable_image_unmodeled :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret EISDIR) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []), ([97, 47, 98], [104])] IEof))
  = check_result.CheckUnmodeled

:= by rfl

/-! The contrast, so the guard is a COMPONENT prefix and not a byte
    prefix: "ab" does not live under "a", and the removal goes through,
    leaving the map in its canonical sorted form ([Fs.fs_remove_sorted]).
    The effect carries the pathname copy-in the spec records — two bytes,
    'a' and the NUL — without which the checker rejects it. -/
theorem unlinkat_byte_prefix_is_not_a_directory :
  (match check_syscall
          (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a (fun _ => none))
          (with_copyins [(8192, 2)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []), ([97, 98], [104])] IEof)) with
  | check_result.CheckOk m [] => m_fs m = [([97, 98], [104])]
  | _ => False
  )

:= by rfl

/- ---------------------------------------------- where the ledger starts

   The copy-in boundary is a CHOICE, and wrapping the whole spec in a
   ledger rather than only the arms past [read_cstr] would satisfy every
   case above just as well.  These four pin the boundary itself: two on
   either side of it, and two on the extent.

   They matter because [read_cstr]'s extent is the string length, not a
   constant like [prlimit64]'s 16 bytes, so [Fs.Namei.unlinkat_spec] has
   to compute it.  What pins that computation is a literal here. -/

/-! The flag word is decided BEFORE [getname()], so that arm reads NO
    user memory and its ledger is empty.  A ledger claimed there is a
    read the kernel did not perform.  This is the case a whole-spec
    wrapper gets wrong: it would EXPECT this range and accept. -/
theorem unlinkat_bad_flags_records_no_copyin :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 1, 0, 0, 0] mem_name_a (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret EINVAL) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = check_result.CheckReject

:= by rfl

/-! ...and the same call with an EMPTY ledger is admitted, so the
    rejection above is about the ledger and not about the arm. -/
theorem unlinkat_bad_flags_empty_ledger_ok :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 1, 0, 0, 0] mem_name_a (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [])] IEof)) []

:= by rfl

/-! Past the flag test the ledger is REQUIRED: the removal really did
    read the path, so denying it is a rejection.  Contrast with the case
    above — the two differ in the flag word alone, and the ledger
    obligation flips with it. -/
theorem unlinkat_removal_needs_the_copyin :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a (fun _ => none))
    (mkEffect 0 [] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []), ([97, 98], [104])] IEof))
  = check_result.CheckReject

:= by rfl

/-! And the EXTENT is the NUL-terminated prefix — 'a' and the NUL, two
    bytes.  One byte short is the name without its terminator, which is
    not what [getname()] reads; the checker rejects it. -/
theorem unlinkat_copyin_extent_is_the_nul_terminated_prefix :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a (fun _ => none))
    (with_copyins [(8192, 1)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], []), ([97, 98], [104])] IEof))
  = check_result.CheckReject

:= by rfl

/- --------------------------------------- the two arms typed by the walk

   [Fs.Namei.unlinkat_spec] answers a TRAILING separator and an
   all-separator path without a directory structure, because the kernel
   settles both without one either.  The four cases below pin each from
   both sides.  A real run can only show the checker what the kernel
   actually did, so it exercises the accepting half of an arm and never
   the rejecting half — no program can make Linux remove a file through
   a name with a trailing separator. -/

/-! Path bytes at 8192: 'a', '/', NUL. -/
def mem_name_a_slash : word → Option byte :=
  fun a => if bv_eqb a 8192 then some 97        /- 'a' -/
           else if bv_eqb a 8193 then some 47   /- '/' -/
           else if bv_eqb a 8194 then some 0    /- NUL -/
           else none

/-! Path bytes at 8192: '/', NUL — a path with no component at all. -/
def mem_name_root : word → Option byte :=
  fun a => if bv_eqb a 8192 then some 47        /- '/' -/
           else if bv_eqb a 8193 then some 0    /- NUL -/
           else none

/-! "a/" names the same component "a" as "a" does, but [do_unlinkat]
    tests the byte just past it and jumps to its [slashes:] label, which
    for a regular file is -ENOTDIR.  The file survives: the answer is
    reached from ABOVE [vfs_unlink]. -/
theorem unlinkat_trailing_slash_on_a_file_is_enotdir :
  (match check_syscall
          (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a_slash (fun _ => none))
          (with_copyins [(8192, 3)] (mkEffect (errno_ret ENOTDIR) [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof)) with
  | check_result.CheckOk m [] => m_fs m = [([97], [104])]
  | _ => False
  )

:= by rfl

/-! The rejecting half: a kernel that removed the file through "a/" and
    returned 0 is a kernel this model must not admit.  Without the
    [path_trailing_slash] test this case is the ordinary removal and
    accepts, so this is what separates the two spellings of the arm. -/
theorem unlinkat_trailing_slash_success_rejected :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_name_a_slash (fun _ => none))
    (with_copyins [(8192, 3)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [([97], [104])] IEof))
  = check_result.CheckReject

:= by rfl

/-! "/" has no component, so [link_path_walk] leaves the type at its
    initial LAST_ROOT and [do_rmdir]'s [case LAST_ROOT] answers -EBUSY.
    The file system is not consulted, so an EMPTY map gives the same
    answer as any other. -/
theorem unlinkat_root_removedir_is_ebusy :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 512, 0, 0, 0]   /- AT_REMOVEDIR -/ mem_name_root (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret EBUSY) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []

:= by rfl

/-! The rejecting half, and the one that matters most: -ENOENT is the
    answer the flat map WOULD give on its own — "no such key" — and it is
    the confident wrong one.  Linux never answers -ENOENT for "/". -/
theorem unlinkat_root_enoent_rejected :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 512, 0, 0, 0]   /- AT_REMOVEDIR -/ mem_name_root (fun _ => none))
    (with_copyins [(8192, 2)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckReject

:= by rfl

/- ------------------------------------------ an absolute name under /tmp

   A program may write a temporary file and then unlink it by an
   ABSOLUTE name under /tmp.  The /tmp arm answers that shape: the
   removal of a key the run holds, and the -ENOENT of one it does not.
   The cases below pin both from the sides a real run cannot reach.  An
   absolute name under any OTHER directory is still the separator
   guard's decline.

   The shape is worth separating from that decline because the two prices
   [Sys.Fs.Namei.unlinkat_spec]'s WORLD note puts on an interior
   separator do not buy it between them.  A component walk over the
   existing keys answers a name INSIDE the working directory's subtree; a
   recorded working-directory path relates an absolute name to one.  This
   name is neither: its parent is a directory the working directory does
   not contain, so with both paid the map still holds no key for it.
   Closing it in general is the third price the note names — directories
   as state in their own right — and what this arm does INSTEAD is rest
   on the privacy premise, which buys /tmp and nothing else. -/

/-! The pathname bytes of "/tmp/out.gif" at 8192, NUL-terminated.  A
    [bytes_at] literal rather than [mem_name_a_slash]'s if-chain, which
    stops being readable well before thirteen bytes. -/
def abs_gif_name : List byte :=
  [47, 116, 109, 112, 47, 111, 117, 116, 46, 103, 105, 102]

def mem_abs_gif : word → Option byte :=
  bytes_at 8192 (abs_gif_name ++ [0])

/-! The name alone, without its directory: "out.gif". -/
def mem_gif_basename : word → Option byte :=
  bytes_at 8192 ([111, 117, 116, 46, 103, 105, 102] ++ [0])

/-! The same call on a name the run does not hold: the empty
    image the model starts a run with and an EMPTY declared /tmp.  The
    path is one the /tmp arm names — one component under "/tmp/" — so the
    separator gate is not what answers it.  The run declared nothing at
    that name and created nothing there, and the privacy premise makes
    the run's own table the whole truth about the directory, so the
    answer is the real -ENOENT Linux gives for a negative dentry.
    Nothing moves — the model handed back is the one
    handed in — and the success a kernel holding the file would return is
    refused, which is what keeps the answer from being a licence to
    remove. -/
theorem unlinkat_tmp_key_not_held_is_enoent :
  let m0 := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  let call eff := check_syscall
        (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_abs_gif (fun _ => none))
        (with_copyins [(8192, 13)] eff) m0 ;
  call (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckOk m0 []
  ∧ call (mkEffect 0 [] []) = check_result.CheckReject

:= by constructor <;> rfl

/-! THE SECOND UNLINK: a key the run DECLARED and then removed ITSELF.
    The first call takes the key out and returns 0; the second reads the
    table that call left and answers -ENOENT, and a second success is
    refused.

    THIS CASE IS DOCUMENTARY, and saying so is worth more than a
    stronger-sounding claim.  It distinguishes no kernel this file does
    not already distinguish: its first two conjuncts are
    [unlinkat_tmp_declared_key_removed] below on the same fixture, and
    since the arm reads only [m_fs], the model that removal leaves is
    indistinguishable to it from the empty one
    [unlinkat_tmp_key_not_held_is_enoent] above is stated over.  What it
    records is the COMPOSITION a program that cleans up after itself
    makes, written down in one place because its two halves are proved
    separately.  A case that bit on its own would have to leave a SECOND
    declared component behind the removal, so that the post-removal model
    is one no other case reaches. -/
theorem unlinkat_tmp_removed_key_second_unlink_is_enoent :
  let call eff m := check_syscall
        (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_abs_gif (fun _ => none))
        (with_copyins [(8192, 13)] eff) m ;
  (match call (mkEffect 0 [] [])
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp [] [([111, 117, 116, 46, 103, 105, 102], [104])]
                IEof)) with
  | check_result.CheckOk m1 [] =>
      m_fs m1 = []
      ∧ call (mkEffect (errno_ret ENOENT) [] []) m1 = check_result.CheckOk m1 []
      ∧ call (mkEffect 0 [] []) m1 = check_result.CheckReject
  | _ => False
  )

:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE REMOVAL ITSELF, over a /tmp the run DECLARED ([State.in_tmp]
    carrying the one component "out.gif", which [State.fs_seed_tmp]
    seeds under "/tmp/").  The key is gone afterwards, and nothing else
    moved. -/
theorem unlinkat_tmp_declared_key_removed :
  (match check_syscall
          (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_abs_gif (fun _ => none))
          (with_copyins [(8192, 13)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit
             (demo_input_tmp [] [([111, 117, 116, 46, 103, 105, 102], [104])] IEof)) with
  | check_result.CheckOk m [] => m_fs m = []
  | _ => False
  )

:= by rfl

/-! The SAME image written as a raw key rather than as a declaration.
    The two are one model — the seeding puts the declared component
    under "/tmp/" and nowhere else — so the arm cannot tell a declared
    entry from an image key that spells the same path, and this case is
    what says so.  It also records the reading the /tmp arm gives: a
    "/tmp/"-prefixed key IS the file in the run's private /tmp. -/
theorem unlinkat_tmp_image_key_removed :
  (match check_syscall
          (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_abs_gif (fun _ => none))
          (with_copyins [(8192, 13)] (mkEffect 0 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof)) with
  | check_result.CheckOk m [] => m_fs m = []
  | _ => False
  )

:= by rfl

/-! What stays declined under /tmp, each on the image that HOLDS the
    key, so that none of them is declining for want of the file.

    AT_REMOVEDIR is declined: Linux answers -ENOTDIR here (a model file
    is never a directory), and the working-directory arm says so, but
    which answer it is turns on /tmp holding a directory, which the /tmp
    arm does not model.  A second component needs a walk.  "/tmp"
    itself, "/tmp/" and "/tmp/." name the directory rather than a file
    in it. -/
theorem unlinkat_tmp_excluded_shapes_unmodeled :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input [(abs_gif_name, [104]), ([47, 116, 109, 112, 47, 100, 47, 102], [104])] IEof) ;
  let call mem n flags eff := check_syscall
        (SyscallInput.mkInput 35 [AT_FDCWD, 8192, flags, 0, 0, 0] mem (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  /- AT_REMOVEDIR at the very name the plain flag removes -/
  call mem_abs_gif 13 512 /- AT_REMOVEDIR -/ (mkEffect (errno_ret ENOTDIR) [] []) = check_result.CheckUnmodeled
  /- a second component, "/tmp/d/f", whose key the image holds -/
  ∧ call (bytes_at 8192 ([47, 116, 109, 112, 47, 100, 47, 102] ++ [0])) 9 0
       (mkEffect 0 [] []) = check_result.CheckUnmodeled
  /- the directory itself, in its three spellings -/
  ∧ call (bytes_at 8192 ([47, 116, 109, 112] ++ [0])) 5 0
       (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckUnmodeled
  ∧ call (bytes_at 8192 ([47, 116, 109, 112, 47] ++ [0])) 6 0
       (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckUnmodeled
  ∧ call (bytes_at 8192 ([47, 116, 109, 112, 47, 46] ++ [0])) 7 0
       (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckUnmodeled
  ∧ call (bytes_at 8192 ([47, 116, 109, 112, 47, 46, 46] ++ [0])) 8 0
       (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckUnmodeled

:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A DIRECTORY INSIDE /tmp, which the flat map only implies: the
    declaration names "d/f", so a key lives under "/tmp/d" and
    [Fs.Namei.fs_under] sees it there.  Linux refuses to unlink a
    directory in [may_delete], which [vfs_unlink] calls before it
    removes anything, so the answer is -EISDIR and the model does not
    move.  The removal a flat map would have performed is refused
    beside it.

    THE TRAILING-SEPARATOR SPELLING IS THE SAME ANSWER BY A DIFFERENT
    ROUTE, which is why it is worth pinning next to the plain one: the
    model strips the separator and reaches the same arm, and Linux does
    not — it jumps to [do_unlinkat]'s [slashes:] label, whose own
    [d_is_dir] test answers -EISDIR for a directory.  (fs/namei.c, Linux
    v6.18.46.) -/
theorem unlinkat_tmp_implied_directory_is_eisdir :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100, 47, 102], [104])] IEof) ;
  let call mem n eff := check_syscall
        (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  let dir := bytes_at 8192 ([47, 116, 109, 112, 47, 100] ++ [0]) ;
  let dir_slash := bytes_at 8192 ([47, 116, 109, 112, 47, 100, 47] ++ [0]) ;
  call dir 7 (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk m0 []
  ∧ call dir 7 (mkEffect 0 [] []) = check_result.CheckReject
  ∧ call dir_slash 8 (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk m0 []
  ∧ call dir_slash 8 (mkEffect 0 [] []) = check_result.CheckReject

:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ORDER OF THE TWO /tmp RULES, which is the whole of what keeps
    the answer above right.  "/tmp/d" is not a key the run HOLDS — the
    declaration named "d/f" and nothing else — so the rule that answers
    a name the run does not hold would call it -ENOENT, and Linux calls
    it -EISDIR.  [Fs.Namei.unlinkat_tmp_spec] tests [fs_under] BEFORE
    the lookup, so the directory wins; this case is what says the two
    rules are in that order and not the other one, by refusing the
    -ENOENT.

    The honest twin is the second half: at a name with nothing under it,
    the not-held rule still fires and -ENOENT is still the answer.
    Without it a spec that answered -EISDIR for every absent name under
    /tmp would pass the first half. -/
theorem unlinkat_tmp_implied_directory_precedes_not_held :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp [] [([100, 47, 102], [104])] IEof) ;
  let call mem n eff := check_syscall
        (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem (fun _ => none))
        (with_copyins [(8192, n)] eff) m0 ;
  let dir := bytes_at 8192 ([47, 116, 109, 112, 47, 100] ++ [0]) ;
  /- the implied directory: -ENOENT is REFUSED, -EISDIR is the answer -/
  call dir 7 (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckReject
  ∧ call dir 7 (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckOk m0 []
  /- a name with nothing under it: the not-held rule still answers -/
  ∧ call mem_abs_gif 13 (mkEffect (errno_ret ENOENT) [] []) = check_result.CheckOk m0 []
  ∧ call mem_abs_gif 13 (mkEffect (errno_ret EISDIR) [] []) = check_result.CheckReject

:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE OTHER HONEST TWIN: the -EISDIR does not leak onto a sibling.
    On a /tmp declaring both the nested "d/f" and a plain "out.gif", the
    plain key is still REMOVED and the nested declaration is still
    seeded at its own key — [State.in_tmp] does not forbid a separator
    in a declared name. -/
theorem unlinkat_tmp_implied_directory_sibling_still_unlinks :
  let m0 := init_model [] 0 0 demo_sp demo_limit
              (demo_input_tmp []
                 [([100, 47, 102], [104]),
                  ([111, 117, 116, 46, 103, 105, 102], [104])] IEof) ;
  fs_lookup (m_fs m0) [47, 116, 109, 112, 47, 100, 47, 102] = some [104]
  ∧ (match check_syscall
             (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_abs_gif (fun _ => none))
             (with_copyins [(8192, 13)] (mkEffect 0 [] [])) m0 with
     | check_result.CheckOk m [] =>
         fs_lookup (m_fs m) abs_gif_name = none
         ∧ fs_lookup (m_fs m) [47, 116, 109, 112, 47, 100, 47, 102] = some [104]
     | _ => False
     )

:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE [Uapi.NAME_MAX] BOUNDARY on this arm, from both sides, as the
    openat twin has it ([Checks.Cases.Fs.Open.openat_tmp_name_max_boundary]).
    Both arms have to draw the line at the same place, since "held" is
    one predicate over one key space: a component the open can mint and
    the unlink cannot remove would be a file the run could not get rid
    of.  So a component of 255 bytes is REMOVED and one of 256 is
    DECLINED, over a declaration holding each. -/
theorem unlinkat_tmp_name_max_boundary :
  let name n := List.replicate n (Z_to_bv 8 97) ;
  let call n := check_syscall
        (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0]
           (bytes_at 8192 ([Z_to_bv 8 47, Z_to_bv 8 116, Z_to_bv 8 109,
                            Z_to_bv 8 112, Z_to_bv 8 47] ++ name n
                           ++ [Z_to_bv 8 0])) (fun _ => none))
        (with_copyins [(8192, (6 + n))] (mkEffect 0 [] []))
        (init_model [] 0 0 demo_sp demo_limit
           (demo_input_tmp [] [(name n, [Z_to_bv 8 104])] IEof)) ;
  /- 255: the key the declaration seeded is removed -/
  (match call 255 with | check_result.CheckOk m [] => m_fs m = [] | _ => False )
  /- 256: declined, though the run holds the key just the same -/
  ∧ call 256 = check_result.CheckUnmodeled

:= by constructor <;> rfl

/-! A NAME the declaration could not put anywhere: a component with a
    NUL byte in it.  [State.fs_seed_tmp] drops it, so the run holds
    nothing at that name, and no pathname could reach it in any case —
    [Uaccess.read_cstr] stops at the NUL, so the path this call passes is
    "/tmp/o", not "/tmp/o\0ut".  The declaration is not an image the
    model can be surprised by. -/
theorem unlinkat_tmp_nul_name_is_not_seeded :
  m_fs (init_model [] 0 0 demo_sp demo_limit
          (demo_input_tmp [] [([111, 0, 117, 116], [104])] IEof)) = []

:= by rfl

/-! The rejecting half, reached through the name the walk WOULD end at.
    "out.gif" carries no separator, so it is answered rather than
    declined — and on the image above it is answered -ENOENT, because
    [Fs.Namei.fs_under] is a COMPONENT prefix and "/tmp/out.gif" does not
    live under "out.gif".  A kernel that removed something through it is
    not admitted.  Without this the two cases above are consistent with a
    model that reads the flat map as a directory tree. -/
theorem unlinkat_absolute_basename_success_rejected :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_gif_basename (fun _ => none))
    (with_copyins [(8192, 8)] (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof))
  = check_result.CheckReject

:= by rfl

/-! ...and the answer it does admit, so the rejection above is about the
    removal and not about the ledger. -/
theorem unlinkat_absolute_basename_is_enoent :
  check_syscall
    (SyscallInput.mkInput 35 [AT_FDCWD, 8192, 0, 0, 0, 0] mem_gif_basename (fun _ => none))
    (with_copyins [(8192, 8)] (mkEffect (errno_ret ENOENT) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [(abs_gif_name, [104])] IEof)) []

:= by rfl

end LinuxSem.Checks.Cases.Fs.Namei
