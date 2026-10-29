/-
  * LinuxProcessSem.Sys.Fs.Namei — unlinkat (35)


  This file answers to Linux `fs/namei.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.v` carries the whole map.

  `.` is the only path constant more than one syscall file needs, so it
  does not live in any of them: `Uapi.dot_path` defines it, and
  `openat`, `newfstatat` and the `unlinkat` here all read it from
  there rather than from each other.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.v` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  What each dependency supplies:

      From LinuxSem.LinuxProcessSem Require Import BvBase Fs State Monad.
      From LinuxSem.LinuxProcessSem.Sys Require Export Syscall Uapi.

  Here `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
  so every spec's type is `SysSpec SyscallEffect`, `getModelSpec`/`inputSpec`
  are the monad's state and input steps, and `seqSpec` is the `;;` that
  discards a unit
  result.  `StateMemory` supplies `read_cstr`, `cstr_access_len_aux` and
  `path_max`; `StateLedger` supplies `m_fds`, `m_fs`, `with_fs`;
  `StateInit` supplies `tmp_prefix` and `tmp_key`; `Fs` supplies
  `Fs.path`, `Fs.path_eqb`, `Fs.fs_lookup`, `Fs.fs_remove` and
  `Fs.path_slash_byte`; `Sys.Syscall` supplies `ret_only`, `err_ret`,
  `record_copyins`, `errno_from`, `flag32` and `Syscall.abi_low32`;
  `Sys.Uapi` supplies `AT_FDCWD32`, `AT_REMOVEDIR`, `dot_path` and
  `NAME_MAX`; the errno constants (`ENOENT`, `EISDIR`, ...) come from
  `State.lean` through `MonadInstances`.

  `set_fs`.  `set_fs` is `modify (with_fs fs)`.  `Monad.lean` does not carry the state setters,
  so this file spells it once at the top, exactly as `Sys/Fs/Open.lean`
  and `Sys/Fs/ReadWrite.lean` do; the definitions are identical and
  keeping each spec file independent of its siblings is what lets the
  integrator wire them in any order.

  NOTATION.  `x <- c ;; k` is `bind c (fun x => k)`
  here; `Z` is `Int`, `word` is `BitVec 64`, `byte` is `BitVec 8`,
  `Z_to_bv 64 n` is `BitVec.ofInt 64 n`, `bv_unsigned w` is
  `(w.toNat : Int)`, `negb b` is `!b`, `Nat.eqb a b` is `a == b`,
  `Nat.ltb a b` in a `bool` definition is `decide (a < b)`, and
  `firstn` is `List.take`.

  `Forall`.  `Forall P l` is spelled `∀ x ∈ l, P x`
  (`fs_under_false_of_keys` below), as `Fs.lean`'s header records: the
  Lean 4.31 core library has no `List.Forall`, and this is the same
  predicate at the same place.

  THE CHECKS.  This module is eighteen definitions, five lemmas and their
  prose; it contains no closed-goal check.  All of them are here, in order.  The two `private` lemmas in the scaffolding
  section (`unlink_rmdir_noFlags`, `unlink_rmdir_removedir`) and the
  three `unlinkat_spec_*` introduction lemmas are PORT SCAFFOLD, not
  restatements: they are the same introduction
  steps `Sys/Fs/Stat.lean` takes inline for `newfstatat_spec`, spelled
  once here because every check at the end of the file needs them.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.StateInit
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Namei

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

/- =========================================================================
   `Monad.v`'s `set_fs`, spelled once (NOTE)
   ========================================================================= -/

/-- `set_fs`: install a new interpreted file system. -/
def set_fs (fs : Fs.Fs) : SysSpec Unit := modifySpec (with_fs fs)

/- =========================================================================
   The path constants and the component tests
   ========================================================================= -/

/-- `..` — the parent directory.  Like `.`, it is a path the kernel
    answers without consulting any file system: `link_path_walk` types
    the last component, and both `do_unlinkat` and `do_rmdir` branch on
    that type before they look anything up.  Their answers differ, which
    is why the two paths are separate constants here rather than one
    "directory reference" class. -/
def dotdot_path : Fs.path := [BitVec.ofInt 8 46, BitVec.ofInt 8 46]

/-- The separator, as a byte. -/
def slash_byte : byte := BitVec.ofInt 8 47

/-- The SAME byte is spelled in `Fs`, as `Fs.path_slash_byte`, because
    `Fs.key_is_relative` needs it at a rung below this one and this file
    sits above it.  The separator's MEANING stays here — the component
    tests below are what a separator is for — and the two spellings are
    pinned equal so that moving either is a compile error rather than a
    silent divergence. -/
theorem slash_byte_is_path_slash_byte : slash_byte = path_slash_byte := rfl

/-- Does the path contain a component separator? -/
def path_has_slash (p : Fs.path) : Bool :=
  p.any (fun b => bv_eqb b slash_byte)

/-- Used on a REVERSED path, which is what makes it strip trailing
    separators; nothing else calls it. -/
def drop_leading_slashes (p : Fs.path) : Fs.path :=
  match p with
  | [] => []
  | b :: r => if bv_eqb b slash_byte then drop_leading_slashes r else b :: r

/-- Drop the separators a path ENDS with.  `link_path_walk` hashes a
    component, then skips every following "/" and stops if the string
    ends there, so trailing separators never start a component and never
    change which component is the last one (Linux fs/namei.c,
    `link_path_walk`, the `if (!*name) goto OK` / skip-slashes /
    `if (unlikely(!*name))` sequence just after the `LAST_NORM` arm).
    What they DO change is the byte `do_unlinkat` tests as
    `last.name[last.len]`: see `path_trailing_slash`. -/
def path_strip_trailing_slashes (p : Fs.path) : Fs.path :=
  (drop_leading_slashes p.reverse).reverse

/-- Is the last component followed by a separator?  This is the kernel's
    own `last.name[last.len]` — the byte just past the component, which
    is "/" exactly when the path had trailing separators and NUL
    otherwise. -/
def path_trailing_slash (p : Fs.path) : Bool :=
  !((path_strip_trailing_slashes p).length == p.length)

/-- `p` is a DIRECTORY COMPONENT of `q`: `q` is `p` followed by "/" and
    then anything.  The base case is "`p` fully consumed", so the caller
    must not pass the empty path — a stripped path of nothing is the
    LAST_ROOT arm, answered before this is reached. -/
def dir_prefixb (p q : Fs.path) : Bool :=
  match p, q with
  | [], [] => false
  | [], c :: _ => bv_eqb c slash_byte
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_eqb a b && dir_prefixb p' q'

/-- Does any file in `fs` live UNDER `p`?  If one does then `p` names a
    directory — a thing the flat map only implies and cannot hold. -/
def fs_under (fs : Fs.Fs) (p : Fs.path) : Bool :=
  match fs with
  | [] => false
  | (q, _) :: r => dir_prefixb p q || fs_under r p

/-- `dir_prefixb` read back: a `true` exhibits the rest of the key.
    This is what lets a caller holding a fact about the BYTES of a key
    rule the test out — `Run.absolute_divergent_not_seeded` is the one
    that does, for a key the seeding minted under "/tmp/". -/
theorem dir_prefixb_app : ∀ (p q : Fs.path),
    dir_prefixb p q = true → ∃ r, q = p ++ slash_byte :: r := by
  intro p
  induction p with
  | nil =>
      intro q H
      cases q with
      | nil => simp [dir_prefixb] at H
      | cons c q =>
          simp only [dir_prefixb] at H
          have hc : c = slash_byte := (bv_eqb_eq c slash_byte).mp H
          subst hc
          exact ⟨q, rfl⟩
  | cons a p' ih =>
      intro q H
      cases q with
      | nil => simp [dir_prefixb] at H
      | cons b q' =>
          simp only [dir_prefixb, Bool.and_eq_true] at H
          obtain ⟨Hab, Hr⟩ := H
          have hb : a = b := (bv_eqb_eq a b).mp Hab
          subst hb
          obtain ⟨r, hq⟩ := ih q' Hr
          exact ⟨r, by simp [hq]⟩

/-- Neither half of `fs_under` can fire on a list of keys none of which
    continues `p` with a separator.

    NOTE.  `Forall (fun qd => ...) fs` is the `∀ qd ∈ fs, ...`
    premise here (see the file header). -/
theorem fs_under_false_of_keys : ∀ (fs : Fs.Fs) (p : Fs.path),
    (∀ qd ∈ fs, dir_prefixb p qd.1 = false) →
    fs_under fs p = false := by
  intro fs
  induction fs with
  | nil => intro p _; rfl
  | cons qd r ih =>
      intro p H
      obtain ⟨q, d⟩ := qd
      have hq : dir_prefixb p q = false := H (q, d) (by simp)
      have hr : ∀ x ∈ r, dir_prefixb p x.1 = false := fun x hx => H x (by simp [hx])
      simp only [fs_under, hq, Bool.false_or]
      exact ih p hr

/-- Strip a fixed prefix off a path, or say it is not there. -/
def path_strip_prefix (pre p : Fs.path) : Option Fs.path :=
  match pre, p with
  | [], _ => some p
  | _ :: _, [] => none
  | a :: pre', b :: p' =>
      if bv_eqb a b then path_strip_prefix pre' p' else none

theorem path_strip_prefix_app : ∀ (pre p n : Fs.path),
    path_strip_prefix pre p = some n → p = pre ++ n := by
  intro pre
  induction pre with
  | nil =>
      intro p n H
      simp only [path_strip_prefix, Option.some.injEq] at H
      subst H
      rfl
  | cons a pre' ih =>
      intro p n H
      cases p with
      | nil => simp [path_strip_prefix] at H
      | cons b p' =>
          by_cases hab : bv_eqb a b = true
          · have h : a = b := (bv_eqb_eq a b).mp hab
            subst h
            simp only [path_strip_prefix, hab, ite_true] at H
            rw [ih p' n H]
            rfl
          · simp only [path_strip_prefix, hab, Bool.false_eq_true, ite_false] at H
            cases H

/-- THE ONE PATHNAME SHAPE UNDER /tmp THE MODEL ANSWERS FOR: an
    ABSOLUTE path "/tmp/<name>" with exactly one further component.
    `some name` is the component; `none` is every other spelling, and
    every other spelling is declined the way the separator gate declines
    today.

    WHAT IS REJECTED, and why each is rejected rather than answered:

    - a path that does not begin "/tmp/" at all — including a bare
      "/tmp", "/tmp/" with nothing after it, and "/tmpfoo": the run's
      declaration says nothing about them;
    - a name with a further separator in it ("a/b"): that is a second
      component, so the answer would come from a directory the flat map
      cannot hold.  The declaration may still MENTION such a name, and
      then some key lives under "/tmp/a" and the arms see it through
      `fs_under` — which is why they test it;
    - "." and "..", which name /tmp and its parent rather than a file in
      it.  `Open.path_is_dirref`'s arms answer those for a RELATIVE
      path off the working directory; under an absolute prefix they
      would be answers about directories as state, which this arm
      does not model.

    A NAME WITH A NUL IN IT CANNOT ARRIVE HERE: every pathname the specs
    see comes out of `Uaccess.read_cstr`, which stops at the first NUL.
    So this predicate says nothing about NUL, and the seeding
    (`State.fs_seed_tmp`) drops the declared entries no program could
    name.

    The premise the arms rest on is `State.in_tmp`'s. -/
def tmp_name (p : Fs.path) : Option Fs.path :=
  match path_strip_prefix tmp_prefix p with
  | none => none
  | some n =>
      if Fs.path_eqb n [] then none
      else if path_has_slash n then none
      else if Fs.path_eqb n dot_path then none
      else if Fs.path_eqb n dotdot_path then none
      else some n

/-- The gate and the seeding agree on the key: a path this answers for
    is exactly the key `State.fs_seed_tmp` would have put its component
    under.  That is what makes "the name the program used" and "the key
    the run holds" the same thing. -/
theorem tmp_name_key : ∀ (p n : Fs.path), tmp_name p = some n → p = tmp_key n := by
  intro p n H
  unfold tmp_name at H
  split at H
  · cases H
  · rename_i n' Hs
    have happ : p = tmp_prefix ++ n' := path_strip_prefix_app tmp_prefix p n' Hs
    split at H
    · cases H
    · split at H
      · cases H
      · split at H
        · cases H
        · split at H
          · cases H
          · cases H
            simpa [tmp_key] using happ

/-- Is `p` the path of an open file fd?  A file fd records the PATH it
    was opened on (`FdFile`/`FdFileW`), not an inode, so the model cannot
    represent Linux's unlinked-but-still-open file — see `unlinkat_spec`.

    THE NON-FILE ENTRIES ARE ENUMERATED rather than swept up by a
    `| _ :: r =>` catch-all, and the difference is invisible until an
    `FdEntry` constructor is added.  A catch-all here is extensionally
    right today and would still compile after the next constructor while
    silently answering "names no path" for it — the same unsound-accept
    shape `Select.bits_all_pollable` and
    `Net.Socket.sockfd_lookup_errno` enumerate to avoid, and the harder
    one to notice, because the constructors sit INSIDE a cons pattern
    rather than at the head of an arm. Listing them makes the next
    constructor a compile error.

    `FdPipe` answers `false` and that is exact rather than fail-closed:
    a pipe end names no filesystem path at all.  Both ends hang off one
    anonymous inode on the internal `pipe_mnt`, and NEITHER is reached
    through path resolution: `create_pipe_files` builds the WRITE end
    with `alloc_file_pseudo(inode, pipe_mnt, "", O_WRONLY | ...)` and
    then the READ end with `alloc_file_clone` of that same file
    (fs/pipe.c, v6.18.46 — two different allocators, which is why this
    says "neither is a path" rather than naming one of them for both).
    So no `unlinkat` argument can ever denote a pipe end, and there is
    nothing for the decision to be derived from beyond that. -/
def fd_names_path (fds : List (word × FdEntry)) (p : Fs.path) : Bool :=
  match fds with
  | [] => false
  | (_, FdEntry.FdFile q _) :: r => Fs.path_eqb p q || fd_names_path r p
  | (_, FdEntry.FdFileW q _) :: r => Fs.path_eqb p q || fd_names_path r p
  | (_, FdEntry.FdFileA q _) :: r => Fs.path_eqb p q || fd_names_path r p
  | (_, FdEntry.FdFileRW q _) :: r => Fs.path_eqb p q || fd_names_path r p
  | (_, FdEntry.FdChannel _) :: r => fd_names_path r p
  | (_, FdEntry.FdDir) :: r => fd_names_path r p
  | (_, FdEntry.FdSocket _) :: r => fd_names_path r p
  | (_, FdEntry.FdPipe _ _) :: r => fd_names_path r p
  | (_, FdEntry.FdDevNull _ _) :: r => fd_names_path r p
    -- exact, like the pipe end: /dev/null is not a key of `Fs.Fs` —
    -- `Open.openat_spec` declines the open when the map holds one — so
    -- no descriptor of this kind names a path `unlinkat` can reach
  | (_, FdEntry.FdUrandom) :: r => fd_names_path r p
    -- the same for /dev/urandom, for the same reason

/- =========================================================================
   unlinkat's flag words and injectable failures
   ========================================================================= -/

/-- unlinkat's injectable failures: environment conditions the model does
    not track, all of them documented for unlink(2) and all reachable on
    a directory entry this model cannot tell apart from an ordinary one
    — kernel memory (ENOMEM, listed first as the canonical witness), the
    parent directory's write and search permission (EACCES, from
    `may_delete`'s `inode_permission`), a sticky, append-only or
    immutable entry (EPERM, from the two clauses just after it), a
    read-only mount (EROFS, from `mnt_want_write`, which runs before the
    lookup), and a mount point over the entry (EBUSY, from
    `vfs_unlink`'s `is_local_mountpoint` — the one member that needs
    more than an ordinary entry, since the victim has to be a bind-mount
    target in the caller's namespace)
    (Linux fs/namei.c, `may_delete` / `vfs_unlink`, both byte-identical
    v6.10 through v6.16).
    ENOENT is NOT injectable: file existence IS tracked. -/
def unlinkat_errnos : List Int := [ENOMEM, EACCES, EPERM, EROFS, EBUSY]

/-- The flag words `unlinkat_spec` interprets: 0 and AT_REMOVEDIR, which
    is every word the kernel accepts.  Unlike `modeled_open_flags` this
    is not a modeling choice — a word outside it is the kernel's own
    -EINVAL, not `unmodeled`. -/
def modeled_unlink_flags (flags : word) : Bool :=
  ((flag32 flags).toNat : Int) == 0 || ((flag32 flags).toNat : Int) == AT_REMOVEDIR

/-- Which of the two calls this is: `do_rmdir` or `do_unlinkat`. -/
def unlink_rmdir (flags : word) : Bool :=
  ((flag32 flags).toNat : Int) == AT_REMOVEDIR

/-- THE REMOVAL ITSELF, once the key has been found: shared by the
    working-directory arm and the /tmp arm below so that the two
    provably do the same thing to the same key.  `p` is the pathname as
    the program spelled it, which is what `do_unlinkat`'s `slashes:`
    label reads; `c` is the key.

    The AT_REMOVEDIR answer sits here rather than at each caller because
    it is the same answer for both: a model file is never a directory,
    so `may_delete`'s -ENOTDIR is what Linux returns.  The /tmp arm
    never reaches it, having declined AT_REMOVEDIR above. -/
def unlink_found_spec (p c : Fs.path) (flags : word) (m : Model)
    : SysSpec SyscallEffect :=
  if unlink_rmdir flags then err_ret ENOTDIR  -- a model file is never a directory
  else if path_trailing_slash p then err_ret ENOTDIR  -- do_unlinkat's `slashes:`
  else if fd_names_path (m_fds m) c then unmodeled
  else
    alt (bind (errno_from unlinkat_errnos) (fun e => err_ret e))  -- untracked env failure
        (bind (set_fs (fs_remove (m_fs m) c)) (fun _ => ret_only (BitVec.ofInt 64 0)))

/- =========================================================================
   The /tmp arm
   ========================================================================= -/

/-- THE /tmp ARM: removing a file the run HOLDS in its own private
    temporary directory (`tmp_name`, `State.in_tmp`).  It sits inside
    the separator branch below, tested before that branch declines, the
    way `Open.openat_sep_spec`'s arms sit inside openat's.

    WHAT IT ANSWERS BESIDE THE REMOVAL, FIRST: a name some key lives
    UNDER is -EISDIR.  The declaration may name "a/b", and then "/tmp/a"
    is a DIRECTORY in the run's own /tmp; Linux refuses to unlink a
    directory in `may_delete`, which `vfs_unlink` calls before it
    removes anything, and the refusal is unconditional on the
    filesystem — `d_is_dir` on the victim with `isdir` clear is
    -EISDIR.  This is the one answer here that is LINUX-SPECIFIC rather
    than POSIX's: POSIX lets unlink of a directory be -EPERM, and Linux
    chose -EISDIR.  Every supported implementation is a Linux, and
    qemu-user's `unlinkat` is the host kernel's, so the intersection
    design priority 1 (README.md) asks about is -EISDIR on all of them.  The
    -EISDIR is right for a trailing-separator spelling too, by a
    different route: "/tmp/a/" strips to the same `c`, and Linux reaches
    `do_unlinkat`'s `slashes:` label, whose `d_is_dir` test answers
    -EISDIR for a directory.  All fs/namei.c, Linux v6.18.46;
    `may_delete`'s test was read again in v6.12.1, where it stands
    unchanged, so the answer does not turn on the version.

    WHY AN ANSWER AND NOT A DECLINE, which is the `Open.openat_create_spec`
    argument moved one syscall over: the answer is deterministic, it
    does not depend on which filesystem /tmp is on, and it leaves the
    model unchanged, so one image drives a source and a target into the
    same branch.  The guard runs BEFORE the lookup, and because it
    answers, the order is load-bearing rather than tidy: an implied
    directory is not a key the run holds, so the -ENOENT below would
    claim the name is absent where Linux says it is a directory.
    `Checks.Cases.Fs.Namei.unlinkat_tmp_implied_directory_precedes_not_held`
    pins exactly that, and `Checks/Cases/Fs/Namei.lean` carries it under
    the same name — the -EISDIR beside the -ENOENT the lookup would
    otherwise give — so the order is pinned there as well as read off
    the guard's position below.  What the order also covers is the unrealizable
    image `Fs.valid_fs` admits, where "/tmp/a" and "/tmp/a/b" are both
    keys: no reality has both, and the arm answers the directory rather
    than removing the file.

    WHAT IT ANSWERS BESIDE THE REMOVAL: a key the run does NOT hold is
    -ENOENT.  The arm gives the real
    errno rather than leaving the last call of a run that cleans up after
    itself outside the modeled surface.  Linux reaches the same answer
    through `do_unlinkat`: `filename_parentat` walks to the parent, the
    lookup of the last component finds no entry there, and the NEGATIVE
    dentry that comes back is the -ENOENT the ANSWERS discussion below
    already records (Linux fs/namei.c; through v6.14 the test is
    `do_unlinkat`'s own `d_is_negative` at its `slashes:` label, and
    v6.15 moved it into `lookup_one_qstr_excl` — the same answer either
    way, which is what that note says).

    WHAT MAKES IT TRUE HERE, rather than the flat map's confident guess
    that `unlinkat_root_enoent_rejected` warns about, is the privacy
    premise: the run's /tmp is its OWN, so what the environment declared
    (`State.in_tmp`) plus what `Open.create_wronly` created minus what
    this arm removed is the whole truth about what exists there.
    The premise is the WHOLE of
    what carries this answer, and nothing else in the model corroborates
    it.  One thing that looks as though it might does not:
    `Stat.newfstatat_core_spec` answers -ENOENT for a /tmp name the run
    does not hold, but it reaches that off the FLAT MAP, having no /tmp
    arm, no separator guard and no reading of `State.in_tmp` at all — it
    answers the same way for any absent path, which makes it a
    FALSE REJECTION, and it is the confident wrong answer the WORLD note
    below warns about rather than a second reading of the premise.

    `Open.openat_tmp_spec`'s O_RDONLY of a name not held declines.
    Nothing structural keeps it declined — that branch would answer
    one errno and mint no descriptor, the same shape as the branch here —
    so it could be answered off this same premise.

    WHAT IT DECLINES, each for a reason of its own:

    - AT_REMOVEDIR.  Linux answers -ENOTDIR for a regular file, and for
      a directory -ENOTEMPTY or 0; which one it is depends on /tmp
      holding a DIRECTORY, which this arm does not model.  The arm
      declines the flag rather than answering the one case the
      model could judge, and that is the narrower choice.
    - a component over `Uapi.NAME_MAX`.  That -ENAMETOOLONG comes out
      of the FILESYSTEM's own lookup rather than out of fs/namei.c, and
      the model has no filesystem type to ask.  The working-directory
      arm declines it for the same reason, and unlike `Open`'s plain
      arms (see `Open.openat_plain_name`'s note) nothing needs this one
      to answer.

    The name some key lives UNDER is the -EISDIR above.  The
    working-directory arm in `unlinkat_body_spec` declines that shape,
    and the asymmetry is one of SCOPE and nothing deeper: `may_delete` does not care
    which directory the victim is in, so the same derivation would carry
    the plain arm, and moving it there is a change of its own with its
    own examples to re-check.  Where the two arms DO have to agree is
    the key space, and they do — see the NAME_MAX note in
    `Checks.Cases.Fs.Namei.unlinkat_tmp_name_max_boundary`, which
    `Checks/Cases/Fs/Namei.lean` carries: a 255-byte component is
    removed and a 256-byte one declined, over a declaration holding
    each.  The agreement is still read off `Uapi.NAME_MAX` here.

    THERE IS NO IGNORED-FLAG MASK HERE, and none is wanted: unlike
    `Open.open_ignored_flags`, which strips O_CLOEXEC, O_LARGEFILE and
    O_NONBLOCK before every openat arm sees the word, unlinkat's word
    has already been narrowed to exactly 0 or AT_REMOVEDIR by
    `modeled_unlink_flags` in the wrapper, which is the kernel's own
    `SYSCALL_DEFINE3(unlinkat)` test and runs before `getname()`.  So
    the only distinction left for this arm to make is the one
    `unlink_rmdir` makes.

    `dirfd` is not tested here, and does not have to be: the caller
    below has already required AT_FDCWD.  Linux would ignore any dirfd
    for a path of this shape — `filename_parentat` hands an absolute
    name to `path_init`, which sets `nd->path` from the root and never
    reads `dfd` (fs/namei.c) — so a later real-dirfd arm may drop that
    requirement without changing this arm's answers. -/
def unlinkat_tmp_spec (n p c : Fs.path) (flags : word) (m : Model)
    : SysSpec SyscallEffect :=
  if unlink_rmdir flags then unmodeled
  else if decide (NAME_MAX < n.length) then unmodeled
  else if fs_under (m_fs m) c then err_ret EISDIR  -- may_delete's -EISDIR
  else
    match fs_lookup (m_fs m) c with
    | none => err_ret ENOENT     -- absent from the run's own /tmp: real -ENOENT
    | some _ => unlink_found_spec p c flags m

/- =========================================================================
   unlinkat (35)
   ========================================================================= -/

/-- `unlinkat dirfd path flags`: remove a directory entry.  This is the
    one modeled syscall that DELETES from the file system, and the final
    file system is observable (`ExitEv` carries it), so the removal is
    real: `Fs.fs_remove`.  `Fs.fs_remove_sorted` proves that dropping an
    entry PRESERVES the canonical sorted form the `=` comparison needs —
    a property of the operation alone.  Nothing threads
    `Fs.fs_sorted (m_fs m)` along the model step, so that is not a
    property of the states an execution reaches; `Fs.valid_fs` requires
    it of the initial image and the header assumes the rest.

    ORDER, following the kernel's exactly:

    - the flag word first: anything but 0 or AT_REMOVEDIR is -EINVAL,
      before the pathname is fetched.  `SYSCALL_DEFINE3(unlinkat)` is

          if ((flag & ~AT_REMOVEDIR) != 0)
                  return -EINVAL;
          if (flag & AT_REMOVEDIR)
                  return do_rmdir(dfd, getname(pathname));
          return do_unlinkat(dfd, getname(pathname));

      so `getname` is an argument expression on the two return paths
      only and the -EINVAL genuinely precedes it (Linux fs/namei.c,
      byte-identical v5.9 through v6.18).  Note AT_EMPTY_PATH and
      AT_SYMLINK_NOFOLLOW are NOT accepted: they are -EINVAL like any
      other bit.
    - then `getname()`, with all three of its answers, as `openat_spec`
      has them: -ENAMETOOLONG for no NUL within PATH_MAX, -ENOENT for
      the empty string, and -EFAULT for an unmapped byte — the last
      propagated out of `strncpy_from_user` rather than written in
      `getname_flags` itself (Linux fs/namei.c, `getname_flags`; the
      answers are unchanged v6.10 through v6.16, though the body is not
      byte-stable across it);
    - only then the dirfd, resolved in `path_init`: the relative-to-a-
      dirfd modes are not modeled, so any dirfd but AT_FDCWD is
      `unmodeled` — the same treatment `openat_spec` and
      `readlinkat_spec` give it.

    For an UNREADABLE pathname too: an illegal flag word with a NULL or
    unmapped path is -EINVAL, the pathname never fetched.

    THE ANSWERS, once the path is in hand.  What the kernel does first is
    TYPE the last component, in `link_path_walk`, and three of the four
    types it can produce are settled without consulting any file system.
    So they are exact constants here (Linux fs/namei.c v6.18.46,
    `do_unlinkat` / `do_rmdir`, both byte-identical v6.10 through v6.14;
    in v6.15 both changed for one reason, the negative-dentry -ENOENT
    moving into `lookup_one_qstr_excl`, which changes no answer this spec
    gives):

      | last component | type        | flags = 0 | AT_REMOVEDIR |
      | "."            | LAST_DOT    | -EISDIR   | -EINVAL      |
      | ".."           | LAST_DOTDOT | -EISDIR   | -ENOTEMPTY   |
      | none at all    | LAST_ROOT   | -EISDIR   | -EBUSY       |

    -EISDIR on all three comes from `do_unlinkat`'s `type != LAST_NORM`
    test, which does not distinguish them; `do_rmdir` switches on the
    type and does, and its `case LAST_ROOT` is the -EBUSY.

    LAST_ROOT is "the path had no component" — a path that is nothing but
    separators, so "/" and "//" and "///" alike.  `link_path_walk` sets
    `nd->last_type = LAST_ROOT` before it looks at anything, skips the
    leading separators, and returns 0 the moment the string ends there,
    so it never enters the component loop.  That is what separates this
    arm from the "." and ".." ones, which look identical from the
    outside: the loop calls `may_lookup` before it types anything, so
    those two rest on the caller being able to search its own working
    directory and this one does not.  It is not unconditional: the
    APPROXIMATION note below has the condition each type is behind.

    TRAILING SEPARATORS do not change which component is last, and do not
    change its type; `path_strip_trailing_slashes` carries that argument.
    What they change is one byte: `do_unlinkat` tests `last.name[last.len]`, the
    byte just past the component, and jumps to its `slashes:` label when
    that byte is not NUL.

    The two -ENOTDIRs an ordinary name can draw are DIFFERENT kernel
    answers reached down different
    paths, which is why they are separate arms below rather than one.
    The AT_REMOVEDIR one is `may_delete(..., isdir = 1)`'s
    `!d_is_dir(victim)`, reached through `vfs_rmdir`; a model file is
    always a regular file, so rmdir of one never succeeds.  The
    trailing-separator one is `do_unlinkat`'s `slashes:` label, which
    `vfs_unlink` never gets near:

        if (last.name[last.len])
                goto slashes;
        ...
    slashes:
        if (d_is_dir(dentry))
                error = -EISDIR;
        else
                error = -ENOTDIR;

    The -ENOENT column is one answer for a different reason again: an
    absent name never reaches `slashes:` at all, because
    `lookup_one_qstr_excl` returns `ERR_PTR(-ENOENT)` for a negative
    dentry when the caller passed no LOOKUP_CREATE, and neither
    `do_unlinkat` nor `do_rmdir` does (Linux fs/namei.c v6.18.46,
    `lookup_one_qstr_excl`, the `d_is_negative(dentry) && !(flags &
    LOOKUP_CREATE)` test).  That is why the trailing separator is tested
    only on the arm where the lookup FOUND something.

    NONE OF THIS TRANSFERS TO A PATH LOOKUP, and the reason is worth
    stating here because the byte is the same one.  `openat` and
    `newfstatat` reach the last component through `path_lookupat`, which
    calls `lookup_last`:

        static inline const char *lookup_last(struct nameidata *nd)
        {
            if (nd->last_type == LAST_NORM && nd->last.name[nd->last.len])
                    nd->flags |= LOOKUP_FOLLOW | LOOKUP_DIRECTORY;
            return walk_component(nd, WALK_TRAILING);
        }

    `lookup_last` is called from `path_lookupat` and from nowhere else;
    `path_parentat`, which is what `filename_parentat` and therefore both
    unlink callers use, stops at the parent and never invokes it (Linux
    fs/namei.c v6.18.46, `lookup_last` and its one caller).  So the very
    byte that sends `do_unlinkat` to `slashes:` makes a LOOKUP follow
    symlinks and demand a directory: "sym/" is -ENOTDIR to unlink
    whatever the link points at, because `slashes:` tests the dentry's
    own type, and is the link's TARGET to open.  A spec for a lookup must
    therefore not reuse the reasoning above, and must not reuse
    `path_strip_trailing_slashes` on the strength of it.

    THE WORLD this is exact in, and the three guards that keep the spec
    inside it.  The model's file system is a flat map from uninterpreted
    paths to bytes: there is no directory structure, and the only paths
    answered as directories without a lookup are the ones the path walk
    types — ".", "..", and the all-separator LAST_ROOT.  Reality is a
    tree.  The two
    agree exactly when every model key is a regular file directly in the
    working directory AND the working directory holds nothing but those
    keys — the first half is the correspondence `openat_spec` already
    depends on.  The
    SECOND half is the one no guard below can restore, because an EMPTY
    real directory has no key at all: `fs_under` sees nothing under it
    and `fs_lookup` misses, so unlinking it is -EISDIR on Linux and
    -ENOENT here, and an AT_REMOVEDIR of it really succeeds there.
    Trailing separators put MORE inputs behind that precondition without
    changing the precondition itself: "D/" reaches these arms rather
    than the separator decline, so a program that names an
    empty real directory with a trailing separator gets the same
    wrong -ENOENT that naming it plainly gets, instead of an
    honest `unmodeled`.  That is a real cost of answering trailing
    separators, it is the reason those arms stop where they do, and
    it is a divergence kept rather than fixed.  No
    modeled syscall creates a directory — and it cannot, in the order that
    matters: `Fs` maps a path to a byte list, so there is no value a
    created directory could BE, which is why mkdirat is declined and why
    a mkdir cannot land before the representation changes.  What keeps
    this unreached is therefore an ENVIRONMENT precondition and not
    that fact: the run must not start with an empty real directory in
    the working directory.  Where the model
    would otherwise answer with confidence and be wrong, it declines:

    - a path with a "/" ANYWHERE BUT AT THE END is `unmodeled`, once the
      trailing ones are stripped and something is left — leading
      separators included, so an absolute path WITH A COMPONENT is
      declined here.  ("/" and "//" strip to nothing and are the
      LAST_ROOT arm above, not this one.)  The bound is exactly
      "the last component's parent is the working directory": the model
      can type a last component and look it up in the map, and that is
      the whole of what it can do.  A path with a separator anywhere but
      at the end needs the kernel's walk, which resolves every component
      against a tree the flat map does not have — an intermediate name
      that is a regular file is -ENOTDIR, and a last component of "." or
      ".." is typed only after the parent walk succeeds.  An ABSOLUTE
      path is out of reach for a second reason on top of that one:
      nothing in the model records the working directory's own path, so
      "/tmp/x" and "x" cannot be related even when they name one file.
      None of this is a function of the flat map, and the flat map's own
      answer — "that key is absent, -ENOENT" — is the confident wrong
      one.  This is the same gap `Stat.newfstatat_spec` has on the
      stat side, where it is a false REJECTION rather than a decline.

      WHAT CLOSING IT WOULD COST, since "give `Fs` a directory structure"
      is three different jobs with three different prices, and only the
      cheapest is a reinterpretation of what the map already holds:

      - A relative walk that stays WITHIN the working directory's subtree
        is derivable from the existing keys and needs no new state.
        Which non-empty directories exist is already determined —
        `fs_under` is that predicate — so a component walk over it would
        answer "a/b", and the -ENOTDIR of a non-final regular file,
        without `Fs` changing type and so without re-opening any example
        proof.  A ".." that pops ABOVE the working directory is not
        derivable, and for a stronger reason than the next bullet's: not
        only is there no cwd path to resolve it against, `Fs` holds no
        keys outside the working directory at all, so there is nothing
        for the walk to land on.
      - An ABSOLUTE path is not derivable at any price.  It needs the
        working directory's own path, which nothing in the model records.
        Storing one is not the hard part — a cwd is a `Fs.path` like any
        other — the hard part is that the launching directory is chosen
        by the ENVIRONMENT, which makes it a parameter of
        `Equivalence.strong_universal_T` rather than a private field, and
        whoever adds one owes that theorem an accounting.
      - An EMPTY directory is not derivable either, and it is the one
        that cannot be fixed by adding a walk: it leaves NO key in the
        map, so nothing distinguishes it from an absent name.  That is
        why AT_REMOVEDIR can never correctly succeed here, and why
        closing it means directories become state in their own right —
        state a successful rmdir MUTATES, which `ExitEv` would then have
        to carry or the equivalence would quietly coarsen.

      No widening of this spec substitutes for any of the three.

      THE THREE DO NOT COMPOSE.  A program that unlinks the temporary
      file it writes names it absolutely, under a directory the working directory does
      not contain — and that shape is closed by none of the three in
      sequence.  The first answers a name inside the working directory's
      subtree and this name is not one; the second relates an absolute
      name to the working directory and this name's parent is a
      different directory entirely; so the map holds no key for it with
      both paid, and only the third — directories as state in their own
      right — reaches it.  This is a decline reached on every input of
      such a binary, so its `Equivalence.strong_equiv` statement
      is FALSE rather than narrowed, per the `modeled`-in-the-conclusion
      note above.  Widening THIS spec would not by itself make such a
      binary modeled either, while `Open.openat_spec` carries the same
      guard: the create that precedes the unlink leaves the modeled
      surface first on every input that reaches it.
      `Checks/Cases/Fs/Namei.lean` checks that the guard runs ahead of
      the
      lookup (`unlinkat_tmp_implied_directory_precedes_not_held`), and that
      the name the walk would end at is answered rather than declined
      (`unlinkat_tmp_implied_directory_is_eisdir`); the spec's body below
      is what they are checked against.
    - a name longer than `Uapi.NAME_MAX` is `unmodeled`.  `getname()`'s
      PATH_MAX bound lets a 4095-byte single component through, and the
      FILESYSTEM then answers -ENAMETOOLONG; the model has no filesystem
      type to ask.
    - a name some key lives UNDER (`fs_under`) is `unmodeled`.  A key
      "a/b" means reality has a DIRECTORY "a", which the map cannot hold;
      unlinking "a" is -EISDIR there and -ENOENT here.  The guard runs
      before the lookup, so it also covers the unrealizable images
      `Fs.valid_fs` admits, where "a" and "a/b" are both keys.

    THE OPEN-FD GUARD.  Linux keeps an unlinked file's contents reachable
    through an fd already open on it until the last close.  The model's
    file fds record a PATH (`FdFile`/`FdFileW`), not an inode, so after a
    removal they would name nothing — and the read, write, readv and
    writev specs all rest on "an `FdFile` always points into the fs".
    Rather than weaken that invariant in four places, unlinking a path
    some fd still names is `unmodeled` here.  Closing the fd first, which
    is what a program that publishes a file atomically does, stays inside
    the model.

    APPROXIMATION, the same one `openat_spec` carries, in two forms.

    First, and on EVERY deterministic arm: they are deterministic, so
    they exclude `getname_flags`'s own -ENOMEM, which it returns from
    `__getname` before it copies a byte and which is therefore a real
    answer to the empty path, to ".", to "..", to an unreadable pointer
    and to an over-long one.  That is the same shape as `openat_spec`'s
    pre-resolution -EMFILE.

    Second, three untracked conditions sit ahead of these arms, and which
    one reaches which arm follows the last component's TYPE rather than
    the answer:

    - `may_lookup`'s -EACCES: `link_path_walk` calls it at the TOP of the
      component loop, before it hashes anything, so it precedes any arm
      whose path HAS a component.
    - `complete_walk`'s -ESTALE, on a file system defining
      `d_weak_revalidate`: `path_parentat` runs it after the walk, and it
      returns 0 at once unless ND_JUMPED is still set.  `path_init` sets
      that flag, and on this route the LAST_NORM arm of
      `link_path_walk`'s switch is the only thing that clears it
      (`path_lookupat`'s LOOKUP_MOUNTPOINT block also clears it, but
      `filename_parentat` never passes LOOKUP_MOUNTPOINT, so that block
      is not on this route).
    - `mnt_want_write`'s -EROFS, which both `do_unlinkat` and `do_rmdir`
      raise after the type test and before the lookup.

      | arm                    | -EACCES | -ESTALE | -EROFS |
      | LAST_ROOT              | no      | yes     | no     |
      | LAST_DOT, LAST_DOTDOT  | yes     | yes     | no     |
      | LAST_NORM              | yes     | no      | yes    |

    The -ESTALE column runs OPPOSITE to the other two, which is what
    makes it easy to get backwards: the arms that consult no file system
    are the ones still carrying ND_JUMPED, and the LAST_NORM arms that do
    consult one are the arms that cleared it.

    Past those, the arms differ in what ELSE they preempt, because they
    sit at different depths.  The AT_REMOVEDIR -ENOTDIR comes out of
    `may_delete`, so it also preempts the -EACCES and -EPERM that
    function reaches first.  The trailing-separator -ENOTDIR does not:
    `do_unlinkat` jumps to `slashes:` from ABOVE `vfs_unlink`, so
    `may_delete` never runs on that path.  What does precede it is
    `lookup_one_qstr_excl`.  That answers -ENOENT for a working directory
    already removed (`IS_DEADDIR`), and -ENOMEM when it cannot allocate
    the dentry.
    Each of these arms admits one answer and no `unlinkat_errnos`
    alternative, which narrows the spec rather than widening it.

    So LAST_ROOT escapes the first and the third, and is behind
    `complete_walk` alone.  "The answer to \"/\" is unconditional" would
    still be too strong; what is true is that it is the one arm here
    whose answer does not rest on the caller being able to search its own
    working directory. -/
def unlinkat_body_spec (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) : SysSpec SyscallEffect :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => err_ret ENAMETOOLONG        -- no NUL within PATH_MAX
  | .CstrFault => err_ret EFAULT                -- unmapped byte in the path string
  | .CstrOk p =>
      if Fs.path_eqb p [] then err_ret ENOENT  -- empty pathname: getname's own -ENOENT
      else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
      else
        let c := path_strip_trailing_slashes p
        if Fs.path_eqb c [] then                  -- nothing but separators: LAST_ROOT
          (if unlink_rmdir flags then err_ret EBUSY else err_ret EISDIR)
        else if path_has_slash c then
          (match tmp_name c with
           | some n => unlinkat_tmp_spec n p c flags m
           | none => unmodeled  -- a separator not at the end: see WORLD above
          )
        else if Fs.path_eqb c dot_path then
          (if unlink_rmdir flags then err_ret EINVAL else err_ret EISDIR)
        else if Fs.path_eqb c dotdot_path then
          (if unlink_rmdir flags then err_ret ENOTEMPTY else err_ret EISDIR)
        else if decide (NAME_MAX < c.length) then unmodeled  -- the filesystem's own -ENAMETOOLONG
        else if fs_under (m_fs m) c then unmodeled  -- `c` names an implied directory
        else
          match fs_lookup (m_fs m) c with
          | none => err_ret ENOENT               -- absent: real -ENOENT, not a modeling gap
          | some _ => unlink_found_spec p c flags m

/-- The flag word, then the body under its copy-in ledger.

    THE PATHNAME COPY-IN is recorded exactly as `Open.openat_spec`
    records it, and for the same reason: `read_cstr` is a read of user
    memory, and `State.syscall_effect_accesses` turns the ledger into a
    materialization charge, so an unrecorded read is a page the run never
    pays for.  It goes INSIDE the flag test rather than around the whole
    spec as openat's does, because openat's flag arm is `unmodeled` while
    this one is a real -EINVAL the kernel reaches before `getname()` is
    evaluated — recording a copy there would claim a read Linux did not
    perform.  The range is the prefix through the first NUL, the first
    faulting byte, or PATH_MAX, as for openat. -/
def unlinkat_spec (dirfd pathp flags : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
    bind getModelSpec fun m =>
      if !(modeled_unlink_flags flags) then err_ret EINVAL
      else
        record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
          (unlinkat_body_spec dirfd pathp flags i m)

/- =========================================================================
   Port scaffolding: introducing `unlinkat_spec`'s outcome

   `unlinkat_spec` is `input`, then `get_model`, then the flag test, then
   the body under `record_copyins`.  The three lemmas below are the same
   introduction steps `Sys/Fs/Stat.lean` takes for `newfstatat_spec`,
   spelled once because every check at the end of the file needs them.
   ========================================================================= -/

/-- The flag word is accepted, so the body runs under the copy-in ledger. -/
theorem unlinkat_spec_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model)
    (hflags : modeled_unlink_flags flags = true)
    (hcop : eff.eff_copyins = [])
    (hbody : unlinkat_body_spec dirfd pathp flags i m i m (.ok eff m' [])) :
    unlinkat_spec dirfd pathp flags i m
      (.ok (with_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)] eff)
        m' []) := by
  simp only [unlinkat_spec]
  refine bind_ok inputSpec _ i m i m [] _ m' [] rfl ?_
  refine bind_ok getModelSpec _ i m m m [] _ m' [] rfl ?_
  split
  · rename_i hc
    simp [hflags] at hc
  · exact record_copyins_ok_empty hcop hbody

/-- The flag word is not accepted: -EINVAL, before `getname()` runs, so no
    copy-in is recorded. -/
theorem unlinkat_spec_einval (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    (hflags : modeled_unlink_flags flags = false) :
    unlinkat_spec dirfd pathp flags i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp only [unlinkat_spec]
  refine bind_ok inputSpec _ i m i m [] _ m [] rfl ?_
  refine bind_ok getModelSpec _ i m m m [] _ m [] rfl ?_
  split
  · rename_i hc
    exact pure_ok (mkEffect (errno_ret EINVAL) [] []) i m
  · rename_i hc
    simp [hflags] at hc

/-- The body declines: the whole spec declines, ledger and all. -/
theorem unlinkat_spec_unmodeled (dirfd pathp flags : word) (i : SyscallInput)
    (m : Model) (hflags : modeled_unlink_flags flags = true)
    (hbody : unlinkat_body_spec dirfd pathp flags i m i m .unmodeled) :
    unlinkat_spec dirfd pathp flags i m .unmodeled := by
  simp only [unlinkat_spec]
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  split
  · rename_i hc
    simp [hflags] at hc
  · exact record_copyins_unmodeled hbody

/- =========================================================================
   Port checks: the path helpers

   There is no closed-goal check in the reference; these pin the definitions by
   evaluation, as `Fs.lean` does.
   ========================================================================= -/

example : slash_byte = (0x2f : byte) := by decide

/-- A trailing separator is stripped: `a/` splits as `a`. -/
example : path_strip_trailing_slashes [0x61, 0x2f] = [0x61] := by decide

/-- `a/b` has no trailing separator, so it is returned unchanged: the
    separator gate, not this function, is what splits it. -/
example : path_strip_trailing_slashes [0x61, 0x2f, 0x62] = [0x61, 0x2f, 0x62] := by decide

/-- Nothing but separators strips to the empty path — the LAST_ROOT arm. -/
example : path_strip_trailing_slashes [0x2f, 0x2f, 0x2f] = [] := by decide

example : path_strip_trailing_slashes ([] : Fs.path) = [] := by decide

example : path_trailing_slash [0x61, 0x2f] = true := by decide
example : path_trailing_slash [0x61, 0x2f, 0x62] = false := by decide
example : path_trailing_slash ([] : Fs.path) = false := by decide

example : path_has_slash [0x61, 0x2f, 0x62] = true := by decide
example : path_has_slash [0x61, 0x62] = false := by decide
example : path_has_slash ([] : Fs.path) = false := by decide

/-- `a` is a directory component of `a/b`: this is the path split at the
    last slash read as a prefix test. -/
example : dir_prefixb [0x61] [0x61, 0x2f, 0x62] = true := by decide
/-- The same test on the stripped spelling `a/`. -/
example : dir_prefixb [0x61] [0x61, 0x2f] = true := by decide
/-- `ab` does not continue `a` with a separator. -/
example : dir_prefixb [0x61] [0x61, 0x62] = false := by decide
example : dir_prefixb ([] : Fs.path) ([] : Fs.path) = false := by decide
example : dir_prefixb ([] : Fs.path) [0x2f] = true := by decide
example : dir_prefixb [0x61] ([] : Fs.path) = false := by decide

example : fs_under [([0x61, 0x2f, 0x62], [1])] [0x61] = true := by decide
example : fs_under [([0x61, 0x2f, 0x62], [1])] [0x61, 0x2f, 0x62] = false := by decide
example : fs_under ([] : Fs.Fs) [0x61] = false := by decide

example : path_strip_prefix tmp_prefix (tmp_key [0x61]) = some [0x61] := by decide
example : path_strip_prefix tmp_prefix [0x2f, 0x74, 0x6d, 0x70] = none := by decide

/-- `"/tmp/a"` is the one absolute shape the model answers for. -/
example : tmp_name (tmp_key [0x61]) = some [0x61] := by decide
/-- The empty path is not a /tmp name (and never reaches here: the empty
    path is `getname`'s own -ENOENT). -/
example : tmp_name ([] : Fs.path) = none := by decide
/-- A bare `/tmp/` names the directory itself, not a file in it. -/
example : tmp_name (tmp_key ([] : Fs.path)) = none := by decide
/-- `a/b` is a second component: the flat map cannot hold it. -/
example : tmp_name (tmp_key [0x61, 0x2f, 0x62]) = none := by decide
/-- `.` and `..` name /tmp and its parent, not entries in it. -/
example : tmp_name (tmp_key [0x2e]) = none := by decide
example : tmp_name (tmp_key [0x2e, 0x2e]) = none := by decide
/-- `/tmp` without its separator is not the prefix. -/
example : tmp_name [0x2f, 0x74, 0x6d, 0x70] = none := by decide

example : modeled_unlink_flags 0 = true := by decide
example : modeled_unlink_flags (BitVec.ofInt 64 AT_REMOVEDIR) = true := by decide
example : modeled_unlink_flags 1 = false := by decide
example : unlink_rmdir 0 = false := by decide
example : unlink_rmdir (BitVec.ofInt 64 AT_REMOVEDIR) = true := by decide

example : unlinkat_errnos = [ENOMEM, EACCES, EPERM, EROFS, EBUSY] := by decide

example : fd_names_path [(3, FdEntry.FdFile [0x66] 0)] [0x66] = true := by decide
example : fd_names_path [(3, FdEntry.FdFile [0x66] 0)] [0x67] = false := by decide
example : fd_names_path [(3, FdEntry.FdDir)] [0x66] = false := by decide
example : fd_names_path ([] : List (word × FdEntry)) [0x66] = false := by decide

/- =========================================================================
   Port checks: `unlinkat`'s arms

   Every fact the arms turn on is a GROUND computation, so each body proof
   reduces the definitions in place: `unlinkat_ground` is that reduction,
   spelled once.  The unused-simp-argument linter is off for this section
   because one shared reduction list necessarily mentions definitions a
   given arm does not reach.
   ========================================================================= -/

set_option linter.unusedSimpArgs false

/-- An input whose memory holds `bs` at address 0. -/
private def inp (bs : List byte) : SyscallInput :=
  { in_sysno := 35, in_args := [], in_mem := sanityMem bs, in_wmem := fun _ => none }

/-- A model over `fs`, empty descriptor table. -/
private def modelOf (fs : Fs.Fs) : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof fs

/-- `f` as a pathname, NUL-terminated. -/
private def fInput : SyscallInput := inp [0x66, 0]
/-- The empty pathname: its first byte is the NUL. -/
private def emptyInput : SyscallInput := inp [0]
/-- `.` — the working directory. -/
private def dotInput : SyscallInput := inp [0x2e, 0]
/-- `..` — its parent. -/
private def dotdotInput : SyscallInput := inp [0x2e, 0x2e, 0]
/-- `/` — nothing but a separator: LAST_ROOT. -/
private def rootInput : SyscallInput := inp [0x2f, 0]
/-- `f/` — a trailing separator. -/
private def fSlashInput : SyscallInput := inp [0x66, 0x2f, 0]
/-- `/tmp/a`. -/
private def tmpAInput : SyscallInput :=
  inp [0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x61, 0]
/-- `/tmp/a/b` — a separator that is not at the end. -/
private def tmpABInput : SyscallInput :=
  inp [0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x61, 0x2f, 0x62, 0]
/-- `/tmp/z` — not held. -/
private def tmpZInput : SyscallInput :=
  inp [0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x7a, 0]

/-- The flag word 0. -/
private def noFlags : word := 0
/-- The flag word `AT_REMOVEDIR`. -/
private def removedir : word := BitVec.ofInt 64 AT_REMOVEDIR

/-- A file system holding `f`. -/
private def fsF : Fs.Fs := [([0x66], [1, 2, 3])]
/-- A file system holding the /tmp key `/tmp/a/b` only: `/tmp/a` is then an
    implied directory. -/
private def fsTmpAB : Fs.Fs := [(tmp_key [0x61, 0x2f, 0x62], [1])]

/-- The two flag words the checks use, judged by evaluation: `Int`
    equality does not reduce under `simp`, so its answers are lemmas. -/
private theorem unlink_rmdir_noFlags : unlink_rmdir noFlags = false := by decide

private theorem unlink_rmdir_removedir : unlink_rmdir removedir = true := by decide

/-- The definitions a ground `unlinkat` check unfolds. -/
local macro "unlinkat_ground" : tactic =>
  `(tactic| simp [read_cstr, read_cstr_aux, path_max, sanityMem, Fs.path_eqb,
      bv_eqb, path_strip_trailing_slashes, drop_leading_slashes, path_has_slash,
      path_trailing_slash, tmp_name, path_strip_prefix, dir_prefixb, fs_under,
      fs_lookup, fs_remove, fd_names_path, m_fs, m_fds, unlink_found_spec,
      unlinkat_tmp_spec, unlink_rmdir_noFlags, unlink_rmdir_removedir,
      modeled_unlink_flags, flag32, Syscall.abi_low32,
      with_fs, set_fs, modify, modifySpec, pure, ret_only, err_ret,
      errno_from, unlinkat_errnos, alt, bind, unmodeled, mkModel, tmp_key,
      tmp_prefix, dot_path, dotdot_path, slash_byte, NAME_MAX,
      inp, modelOf, fInput, emptyInput, dotInput, dotdotInput, rootInput,
      fSlashInput, tmpAInput, tmpABInput, tmpZInput, fsF, fsTmpAB])

/-- AN EMPTY PATHNAME IS -ENOENT, with `getname`'s copy recorded (the NUL
    it stopped at is one byte). -/
example : unlinkat_spec AT_FDCWD32 0 noFlags emptyInput (modelOf [])
    (.ok (with_copyins [(0, 1)] (mkEffect (errno_ret ENOENT) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags emptyInput (modelOf [])
    (mkEffect (errno_ret ENOENT) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- AN ABSENT NAME IS -ENOENT — the real errno, not a modeling gap. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags fInput (modelOf [])
    (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret ENOENT) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags fInput (modelOf [])
    (mkEffect (errno_ret ENOENT) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- AN ILLEGAL FLAG WORD IS -EINVAL, and carries NO copy-in: the kernel
    answers before `getname()` is evaluated. -/
example : unlinkat_spec AT_FDCWD32 0 1 fInput (modelOf [])
    (.ok (mkEffect (errno_ret EINVAL) [] []) (modelOf []) []) :=
  unlinkat_spec_einval AT_FDCWD32 0 1 fInput (modelOf []) (by decide)

/-- `.` IS -EISDIR for unlink. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags dotInput (modelOf [])
    (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret EISDIR) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags dotInput (modelOf [])
    (mkEffect (errno_ret EISDIR) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- `.` IS -EINVAL for rmdir: `namei.c`'s LAST_DOT case. -/
example : unlinkat_spec AT_FDCWD32 0 removedir dotInput (modelOf [])
    (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret EINVAL) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 removedir dotInput (modelOf [])
    (mkEffect (errno_ret EINVAL) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- `..` IS -EISDIR for unlink. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags dotdotInput (modelOf [])
    (.ok (with_copyins [(0, 3)] (mkEffect (errno_ret EISDIR) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags dotdotInput (modelOf [])
    (mkEffect (errno_ret EISDIR) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- `..` IS -ENOTEMPTY for rmdir: `namei.c`'s LAST_DOTDOT case. -/
example : unlinkat_spec AT_FDCWD32 0 removedir dotdotInput (modelOf [])
    (.ok (with_copyins [(0, 3)] (mkEffect (errno_ret ENOTEMPTY) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 removedir dotdotInput (modelOf [])
    (mkEffect (errno_ret ENOTEMPTY) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- `/` IS -EISDIR for unlink: LAST_ROOT. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags rootInput (modelOf [])
    (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret EISDIR) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags rootInput (modelOf [])
    (mkEffect (errno_ret EISDIR) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- `/` IS -EBUSY for rmdir: `do_rmdir`'s LAST_ROOT case. -/
example : unlinkat_spec AT_FDCWD32 0 removedir rootInput (modelOf [])
    (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret EBUSY) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 removedir rootInput (modelOf [])
    (mkEffect (errno_ret EBUSY) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- A NAME SOME KEY LIVES UNDER IS -EISDIR: `/tmp/a` is implied by the key
    `/tmp/a/b`, and this guard runs BEFORE the lookup. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags tmpAInput (modelOf fsTmpAB)
    (.ok (with_copyins [(0, 7)] (mkEffect (errno_ret EISDIR) [] []))
      (modelOf fsTmpAB) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags tmpAInput (modelOf fsTmpAB)
    (mkEffect (errno_ret EISDIR) [] []) (modelOf fsTmpAB) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- A /TMP NAME THE RUN DOES NOT HOLD IS -ENOENT. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags tmpZInput (modelOf [])
    (.ok (with_copyins [(0, 7)] (mkEffect (errno_ret ENOENT) [] []))
      (modelOf []) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags tmpZInput (modelOf [])
    (mkEffect (errno_ret ENOENT) [] []) (modelOf []) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- A SEPARATOR THAT IS NOT AT THE END IS DECLINED: `/tmp/a/b` needs the
    kernel's walk over a tree the flat map does not have. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags tmpABInput (modelOf []) .unmodeled := by
  refine unlinkat_spec_unmodeled AT_FDCWD32 0 noFlags tmpABInput (modelOf [])
    (by decide) ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- AT_REMOVEDIR OF A REGULAR FILE IS -ENOTDIR (`may_delete`'s
    `!d_is_dir`): a model file is never a directory. -/
example : unlinkat_spec AT_FDCWD32 0 removedir fInput (modelOf fsF)
    (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret ENOTDIR) [] []))
      (modelOf fsF) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 removedir fInput (modelOf fsF)
    (mkEffect (errno_ret ENOTDIR) [] []) (modelOf fsF) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- A TRAILING SEPARATOR ON A FILE THAT EXISTS IS -ENOTDIR TOO, by
    `do_unlinkat`'s `slashes:` label rather than by `may_delete`. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags fSlashInput (modelOf fsF)
    (.ok (with_copyins [(0, 3)] (mkEffect (errno_ret ENOTDIR) [] []))
      (modelOf fsF) []) := by
  refine unlinkat_spec_ok AT_FDCWD32 0 noFlags fSlashInput (modelOf fsF)
    (mkEffect (errno_ret ENOTDIR) [] []) (modelOf fsF) (by decide) rfl ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- AN OPEN FD THAT NAMES THE FILE IS `unmodeled`: the model records the
    path, not an inode, so the unlinked-but-still-open file is not
    representable. -/
example : unlinkat_spec AT_FDCWD32 0 noFlags fInput
    (mkModel [(3, FdEntry.FdFile [0x66] 0)] (mkVmMaps [] [] 0 0 0) IEof fsF) .unmodeled := by
  refine unlinkat_spec_unmodeled AT_FDCWD32 0 noFlags fInput
    (mkModel [(3, FdEntry.FdFile [0x66] 0)] (mkVmMaps [] [] 0 0 0) IEof fsF) (by decide) ?_
  simp only [unlinkat_body_spec]
  unlinkat_ground

/-- THE REMOVAL ITSELF, at the key level: dropping `f` leaves the map empty. -/
example : fs_remove fsF [0x66] = [] := by decide

end LinuxSem.LinuxProcessSem.Sys.Fs.Namei
