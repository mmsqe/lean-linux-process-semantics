/-
  * LinuxProcessSem.Sys.Fs.Open — openat (56), close (57), ftruncate (46),
    faccessat (48), faccessat2 (439)


  This file answers to Linux `fs/open.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.v` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  What each dependency supplies.  `MonadInstances` fixes the concrete
  `Sys Model SyscallInput event`, so every spec's type is
  `SysSpec SyscallEffect`, `getModelSpec`/`inputSpec`/`modifySpec` are the
  monad's state, input and update steps, and `seqSpec` runs a
  `unit`-returning step before the rest.  `StateMemory` supplies `read_cstr`,
  `cstr_access_len_aux` and `path_max`; `StateLedger` supplies `m_fds`,
  `m_fs`, `with_fds`, `with_fs`; `StateMemory`/`StateFd` supply
  `fd_lookup`, `fd_insert`, `fd_remove`; `StateInit` supplies
  `tmp_prefix`; `Fs` supplies `Fs.fs_lookup`, `Fs.fs_set`, `Fs.file_truncate`,
  `path` and `Fs.path_eqb`; `Sys.Fs.File` supplies `lowest_fd` (imported,
  NOT redefined here); `Sys.Syscall` supplies `ret_only`, `err_ret`,
  `record_copyins`, `int32`; `Sys.Uapi` supplies the whole `O_*` flag
  layer, `S_IRWXO`, `AT_*`, `AT_FDCWD32`, `dot_path`, `devnull_path`,
  `urandom_path`, `NAME_MAX` and `z_land`/`z_lor`/`z_ldiff`.

  `Fs.Namei`.  This file's seven path helpers (`dotdot_path`,
  `slash_byte`, `path_has_slash`, `dir_prefixb`, `fs_under`,
  `path_strip_prefix`, `tmp_name`) are the ones `Fs.Namei` owns, carried
  below verbatim and under their own names inside this file's namespace.
  They are the only thing here that does not answer to `fs/open.c`, and
  `Sys/Fs/Namei.lean` now defines the same seven: the copies below are
  staging copies and should be DELETED in favour of that module.  Nothing
  else in this port depends on them.

  `Fs.ReadWrite`.  `Fs.ReadWrite` owns `modeled_zero_fill`, which
  `ftruncate`'s grow guard reuses.  `Sys/Fs/ReadWrite.lean` carries the
  same definition under the same name, so the copy below is a shim and
  should be deleted in favour of the import; nothing else from that file
  is used here.

  `Z.ldiff`.  The bit-difference `a & ~b` is `Sys.Uapi.z_ldiff`, the
  canonical definition beside `z_land`/`z_lor`, imported rather than
  redefined (`Sys.Fs.File.z_ldiff` is a transparent alias to it, kept at
  that file's one caller, `dup3_flags_ok`).

  NOTATION.  `x <- c ;; k` is `bind c (fun x => k)`; `Z` is `Int`,
  `word` is `BitVec 64`, `byte` is `BitVec 8`, `Z_to_bv 64 n` is
  `BitVec.ofInt 64 n`, `bv_unsigned w` is `(w.toNat : Int)`, `bv_signed w`
  is `w.toInt`, `negb b` is `!b`, `beq` is `==`, `firstn` is `List.take`,
  and `Nat.ltb a b` in a `bool` definition is `decide (a < b)`.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.StateInit
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Fs.File

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Open

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File (lowest_fd)

/- =========================================================================
   The `Monad.lean` state setters, spelled once

   `Monad.lean` is parameterized over the model and does not carry
   `set_fds`/`set_fs`; each is `modify (with_fds fds)` /
   `modify (with_fs fs)`.  `Sys/Fs/ReadWrite.lean`
   spells the same two terms in its own namespace, and so does this file:
   the definitions are identical, and keeping each spec file independent
   of its siblings is what lets the integrator wire them in any order.
   ========================================================================= -/

/-- `set_fds`: install a new descriptor table. -/
def set_fds (fds : List (word × FdEntry)) : SysSpec Unit := modifySpec (with_fds fds)

/-- `set_fs`: install a new interpreted file system. -/
def set_fs (fs : Fs.Fs) : SysSpec Unit := modifySpec (with_fs fs)

/- =========================================================================
   The `Fs.Namei` helpers, ported here until that module lands (PORT SHIM)
   ========================================================================= -/

/-- `..` — the parent directory.  Like `.`, it is a path the kernel
    answers without consulting any file system: `link_path_walk` types
    the last component, and both `do_unlinkat` and `do_rmdir` branch on
    that type before they look anything up.  (`Fs.Namei`.) -/
def dotdot_path : Fs.path := [BitVec.ofInt 8 46, BitVec.ofInt 8 46]

def slash_byte : byte := BitVec.ofInt 8 47

/-- The SAME byte is spelled in `Fs`, as `Fs.path_slash_byte`, because
    `Fs.key_is_relative` needs it at a rung below this one and this file
    sits above it.  The separator's MEANING stays here — the component
    tests below are what a separator is for — and the two spellings are
    pinned equal so that moving either is a compile error rather than a
    silent divergence. -/
theorem slash_byte_is_path_slash_byte : slash_byte = Fs.path_slash_byte := rfl

/-- Does the path contain a component separator? -/
def path_has_slash (p : Fs.path) : Bool :=
  p.any (fun b => bv_eqb b slash_byte)

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

/-- Strip a fixed prefix off a path, or say it is not there. -/
def path_strip_prefix (pre p : Fs.path) : Option Fs.path :=
  match pre, p with
  | [], _ => some p
  | _ :: _, [] => none
  | a :: pre', b :: p' =>
      if bv_eqb a b then path_strip_prefix pre' p' else none

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
      would be answers about directories as state, which this arm does
      not model.

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

/- =========================================================================
   openat (56): the flag shapes the model interprets
   ========================================================================= -/

/-- openat's injectable failures: environment conditions the model does
    not track — kernel memory (ENOMEM, listed first as the canonical
    witness), permissions (EACCES), fd-table exhaustion (EMFILE/ENFILE,
    which also keep the spec receptive when no free fd < 2^31 exists).
    ENOENT is NOT injectable: file existence IS tracked, and a missing
    file returns a deterministic -ENOENT. -/
def openat_errnos : List Int := [ENOMEM, EACCES, EMFILE, ENFILE]

/-- The clobbering write-open combination the model covers. -/
def wr_create_flags : Int := O_WRONLY + O_CREAT + O_TRUNC

/-- The EXCLUSIVE write-open combinations the model covers:
    O_WRONLY|O_CREAT|O_EXCL, with or without O_TRUNC.  O_EXCL makes the
    open fail outright when the path already exists, so O_TRUNC can
    never fire alongside it — the two spellings denote exactly the same
    kernel behavior and are modeled by the one branch.  (toybox's
    `cp -n` issues the O_TRUNC spelling; the plain one is what
    mkstemp-style create-if-absent code uses.) -/
def excl_create_flags : Int := O_WRONLY + O_CREAT + O_EXCL

def is_excl_create (fl : Int) : Bool :=
  fl == excl_create_flags || fl == (excl_create_flags + O_TRUNC)

/-- The APPEND write-open combination the model covers:
    O_WRONLY|O_CREAT|O_APPEND, the word C's `fopen(p, "a")` issues (musl
    1.2.6, src/stdio/fopen.c through `__fmodeflags`) and the one zlib's
    gzio output path uses.  It is a SINGLE word and not a mask test: the
    O_TRUNC and O_EXCL spellings beside it are declined, each for its own
    reason, and `modeled_open_flags`'s note says which.

    THIS IS THE ONE ADMITTED WORD WHOSE RESIDUE MEETS
    `Fs.Fcntl.setfl_acted_on`, because O_APPEND is a bit F_SETFL acts
    on.  That is why the fd it mints is a `State.FdFileA` rather than a
    `State.FdFileW`: `Fs.Fcntl.setfl_noop_on` declines the new kind, and
    its arm carries the argument.  A future widening that routed this
    word to `FdFileW` would silently make that predicate unsound. -/
def append_create_flags : Int := O_WRONLY + O_CREAT + O_APPEND

/-- Is bit `b` set in the flag residue `fl`?  Used only by the O_RDWR
    arms, which derive their behavior from the O_CREAT and O_TRUNC bits
    the way `build_open_flags` (fs/open.c, Linux v6.18.46) does, rather
    than from four separate word tests.  The ENVELOPE is still a word
    set (`rdwr_open_word`) and still fails closed outside it; only the
    behavior inside it is read off bits. -/
def flag_set (fl b : Int) : Bool := z_land fl b == b

/-- The READ-WRITE open words the model interprets, other than the
    exclusive ones: O_RDWR alone, and O_RDWR beside O_CREAT, O_TRUNC or
    both.

    WHY ONE PREDICATE AND ONE ARM RATHER THAN FOUR.  The four words
    differ in exactly the two bits `do_open` (fs/namei.c, Linux
    v6.18.46) reads, and each bit changes one answer: O_CREAT decides
    what an ABSENT name gets (a fresh empty file, or the negative
    dentry's -ENOENT out of `lookup_open`), and O_TRUNC decides whether
    an EXISTING file keeps its bytes (`do_open`'s
    `d_is_reg(...) && open_flag & O_TRUNC` arms `handle_truncate`).
    Writing them out four times would repeat one table and let the
    copies drift; `openat_rdwr_spec` is that table.

    O_EXCL IS NOT IN HERE and gets its own arm, because it changes the
    answer to a DIRECTORY REFERENCE as well: `do_open` tests
    `(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)` ahead of
    `d_is_dir`, so "." is -EEXIST under O_EXCL and -EISDIR without it —
    the same asymmetry `is_excl_create` already carries on the
    write-only side. -/
def rdwr_open_word (fl : Int) : Bool :=
  fl == O_RDWR ||
  fl == (O_RDWR + O_TRUNC) ||
  fl == (O_RDWR + O_CREAT) ||
  fl == (O_RDWR + O_CREAT + O_TRUNC)

/-- The EXCLUSIVE read-write create words: O_RDWR|O_CREAT|O_EXCL, with
    or without O_TRUNC.  The two spellings denote the same behavior for
    the reason `is_excl_create` gives on the write-only side — O_EXCL
    fails outright on an existing path, so O_TRUNC can never fire beside
    it — and this is the word musl's `mkostemps` issues, which strips
    the caller's access mode and hardcodes O_RDWR (src/temp/mkostemps.c,
    musl 1.2.6). -/
def rdwr_excl_create_flags : Int := O_RDWR + O_CREAT + O_EXCL

def is_rdwr_excl_create (fl : Int) : Bool :=
  fl == rdwr_excl_create_flags || fl == (rdwr_excl_create_flags + O_TRUNC)

/-- The flag bits every modeled shape accepts and ignores.  Each is
    ignorable for its own reason, recorded at its own definition in
    `Uapi`; the mask exists so that every mirror of the flag test —
    `openat_resolved_spec`, `Checks.Sys.Fs.Open.check_openat` and
    `Checks.Witness.Fs.Open.openat_witness` — strips exactly the same
    bits, and so that widening the set is one edit rather than a
    search. -/
def open_ignored_flags : Int := O_CLOEXEC + O_LARGEFILE + O_NONBLOCK

/-- The flag WORDS `openat_spec` interprets: O_RDONLY, the clobbering
    write-create shape, the exclusive write-create shapes, the
    read-a-directory shape O_RDONLY|O_DIRECTORY, the APPEND
    write-create shape, and the READ-WRITE shapes (`rdwr_open_word` and
    `is_rdwr_excl_create`), each modulo the bits in
    `open_ignored_flags`.
    Linux validates
    the flags in `build_open_flags()` BEFORE it fetches the pathname, so
    this test runs first in `openat_spec` too — see the ORDER paragraph
    there.

    O_DIRECTORY IS INTERPRETED, NOT IGNORED, and it is the only flag here
    that is neither an access mode nor a creation flag.  The reason it
    can be admitted at all is that its answer does not depend on WHICH
    non-directory the name turned out to be.  `do_open` (fs/namei.c)
    answers -ENOTDIR for a dentry `d_can_lookup` (include/linux/dcache.h)
    refuses, and does it before `may_open` (fs/namei.c) and `vfs_open`
    (fs/open.c) run, so the FIFO, device-node and socket cases all
    reach the same errno as a regular file.  The regular-file premise that arm rests on
    is therefore not load-bearing HERE — see `openat_dir_spec`.  Linux
    v6.18.46.

    DELIBERATELY STILL DECLINED.  Two flags real programs reach for that
    this set does NOT admit, each for its own reason, and three
    O_APPEND SPELLINGS beside the one that is admitted:

    - O_WRONLY|O_APPEND without O_CREAT is a different syscall answer,
      not a different name for the same one: the file must already
      exist, and an absent path is a deterministic -ENOENT rather than a
      creation.  The arm is small and is simply not written; a program
      reaching for it gets `unmodeled` rather than a guess.
    - O_WRONLY|O_CREAT|O_TRUNC|O_APPEND is declined because the two
      positioning rules would have to be composed: the file is emptied
      at open and then appended to.  The composition is easy to state
      and the resulting fd is indistinguishable from an append fd on a
      file the open just emptied — which is exactly why it is worth an
      arm of its own with its own test rather than being folded in
      here on the strength of that sentence.
    - O_WRONLY|O_CREAT|O_EXCL|O_APPEND cannot open an existing file at
      all, so the append rule never has an existing tail to append to;
      it is declined for the same reason as the O_TRUNC spelling, being
      a shape no test in this repository exercises.

    - O_RDWR IS ADMITTED, in the six words `rdwr_open_word` and
      `is_rdwr_excl_create` name, and `State.FdFileRW` is its
      read-write kind.  What is declined is O_RDWR
      beside a flag whose own arm is missing rather than beside a bit
      this model cannot represent: O_RDWR|O_APPEND in any spelling
      (the append positioning rule and the read direction have no
      combined arm and no test), O_RDWR|O_DIRECTORY (which
      `build_open_flags` does not reject, and which is -EISDIR on a
      real directory through `may_open`'s MAY_WRITE test — an arm
      nothing here reaches, since `openat_dir_spec`'s guards were
      written for the read-only word), and O_RDWR|O_EXCL WITHOUT
      O_CREAT, which Linux treats as plain O_RDWR (open(2): O_EXCL
      "is undefined" without O_CREAT and `do_open` reads it only inside
      its `open_flag & O_CREAT` block) and which no reported program
      issues, so it is declined rather than aliased.

    - O_NOCTTY is declined because the single thing that makes it
      MEANINGFUL is a terminal, and this model has none.  A program that
      passes O_NOCTTY is opening something it believes is a tty;
      answering it with regular-file semantics would be a confident
      wrong answer where `unmodeled` is the true one.  `tty_open`
      (drivers/tty/tty_io.c) is the site that gives the flag that
      meaning, and `do_dentry_open` (fs/open.c) strips it from `f_flags`
      once the file's `->open` has run, so a program cannot read it back
      afterwards either.

      The reason is deliberately NOT "the flag is inert away from a
      terminal", which is very nearly true and not quite.  Grepping the
      v6.17 tree for O_NOCTTY turns up `v9fs_mapped_dotl_flags`
      (fs/9p/vfs_inode_dotl.c), which forwards it to the 9P server as
      P9_DOTL_NOCTTY on a REGULAR-file open, from a `dotl_oflag_map`
      table byte-identical at v4.9, v4.19, v5.4, v5.10, v5.15, v6.1,
      v6.6, v6.12 and v6.17.  Nothing this model can name is 9p, so the
      decision is unaffected — but an inertness claim ranges over the
      whole tree and would have to be re-established at every widening,
      where the terminal argument above does not.

    A SET HIGH HALF is declined too, and that is a narrowing rather than
    a disagreement: `flags` is `int` at the boundary
    (`SYSCALL_DEFINE4(openat, ...)`, fs/open.c, Linux v6.18.46), so
    Linux discards bits 32-63 before `build_open_flags` reads the word,
    while this predicate reads all 64 and is false for anything above
    the interpreted bits, which `openat_spec` turns into `unmodeled`.
    The arguments the model DOES truncate are exactly the callers of
    `Syscall.abi_low32`. -/
def modeled_open_flags (flags : word) : Bool :=
  let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
  fl == 0 || fl == wr_create_flags || is_excl_create fl ||
  fl == O_DIRECTORY || fl == append_create_flags ||
  rdwr_open_word fl || is_rdwr_excl_create fl

/-- One introduction lemma per modeled shape, so a proof that already
    knows which arm it is in can clear the flags guard. -/
theorem modeled_open_flags_rd (flags : word)
    (H : z_ldiff (flags.toNat : Int) open_ignored_flags = 0) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  simp only [H]
  rfl

theorem modeled_open_flags_wr (flags : word)
    (H : z_ldiff (flags.toNat : Int) open_ignored_flags = wr_create_flags) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  simp only [H]
  simp

theorem modeled_open_flags_excl (flags : word)
    (H : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  rw [H]
  simp

theorem modeled_open_flags_append (flags : word)
    (H : z_ldiff (flags.toNat : Int) open_ignored_flags = append_create_flags) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  simp only [H]
  simp

theorem modeled_open_flags_dir (flags : word)
    (H : z_ldiff (flags.toNat : Int) open_ignored_flags = O_DIRECTORY) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  simp only [H]
  simp

theorem modeled_open_flags_rdwr (flags : word)
    (H : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  rw [H]
  simp

theorem modeled_open_flags_rdwr_excl (flags : word)
    (H : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true) :
    modeled_open_flags flags = true := by
  unfold modeled_open_flags
  dsimp only
  rw [H]
  simp

/- =========================================================================
   openat (56): the arms
   ========================================================================= -/

/-- The common result of opening an existing object: either an
    injectable failure, or the lowest free fd followed by `mk`'s model
    update.  The read-file and directory arms below share this exact
    success shape. -/
def open_result_spec (m : Model) (mk : word → Model → Model)
    : SysSpec SyscallEffect :=
  alt (bind (errno_from openat_errnos) (fun e => err_ret e))
      (bind (lowest_fd (m_fds m)) (fun fd =>
        seqSpec (modifySpec (mk fd)) (ret_only fd)))

/-- The effect a modeled WRITE-CREATE open records, shared by the
    clobbering (O_TRUNC) and the exclusive (O_EXCL) shapes so the two
    provably record the same thing: either an errno from
    `openat_errnos` (an environment condition the model does not track;
    this alternative also keeps the spec receptive when no free
    fd < 2^31 exists), or the lowest free fd bound to a write-only fd
    on `p`, with `p` itself (re)created empty in the file system.

    THIS IS WHERE THE MODEL'S REGULAR-FILE PREMISE IS CREATED.  `p` is
    an uninterpreted byte string, so a name the kernel resolves to a
    character device, a FIFO or a kernfs attribute is recorded here as
    an ordinary file, and every later syscall that resolves the fd
    through `Fs.fs_lookup` — `read`, `lseek`, `ftruncate` and `fsync`,
    and `write` for the base it splices onto — answers for a file that
    is not there. -/
def create_wronly (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  alt (bind (errno_from openat_errnos) (fun e => err_ret e))  -- untracked env failure or no free fd
      (bind (lowest_fd (m_fds m)) (fun fd =>
        seqSpec (set_fs (Fs.fs_set (m_fs m) p []))              -- (re)create the file empty
          (seqSpec (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p (BitVec.ofInt 64 0))))  -- write-only fd
            (ret_only fd))))

/-- The two paths that name a DIRECTORY without consulting a file
    system, and so get the same answer on every arm below.

    The walk types the last component and answers both "." and ".."
    out of itself, never calling a filesystem's `->lookup`.  For the
    LAST component on the open path that is `open_last_lookups`, which
    takes its `nd->last_type != LAST_NORM` branch straight to
    `handle_dots` before O_CREAT is considered at all; interior
    components go through `link_path_walk`.  Both fs/namei.c, Linux
    v6.18.46.

    The three answers come from `do_open`, not from `may_open`: with
    O_CREAT set it returns -EEXIST when O_EXCL is on and the file was
    not created, and -EISDIR on `d_is_dir(nd->path.dentry)`, both BEFORE
    `may_open` is reached.  `may_open`'s own S_IFDIR arm is what lets
    the plain O_RDONLY through.  So the read arm's directory fd, the
    clobbering shape's -EISDIR and O_EXCL's -EEXIST are the same three
    answers for both paths.

    THE ONE ANSWER ".." HAS THAT "." DOES NOT.  `follow_dotdot` ends by
    checking `path_connected`, and returns -ENOENT when the parent has
    been disconnected from the mount — reachable only under a bind mount
    of a subdirectory that was since renamed out of the bind root, since
    `path_connected` short-circuits true whenever `mnt->mnt_root ==
    sb->s_root`.  That errno is not in `openat_errnos` and this arm does
    not admit it, so the arm is NARROWER than Linux by exactly that
    case — the same shape as the -ENOMEM approximation this file already
    carries, and a narrowing rather than a wrong answer.

    THE MODEL CAN AFFORD TO ANSWER, which is why this is an arm and not
    a decline: `State.FdDir` carries NO path, so nothing the model can
    then do to the fd distinguishes the two directories — read is
    -EISDIR for either, close is close, lseek is declined, and
    `Fs.Readdir.getdents64_spec` declines the listing and gives both the
    same -EINVAL where the buffer has no room for an entry.  A decline is
    for what the model cannot judge; it judges this correctly.
    `Fs.Open.faccessat_body_spec` answers ".." the same way and for the
    same reason.

    THE CONDITION THAT WOULD FALSIFY THAT, written here because it is
    what a later directory change has to re-check.  The reason ".." is
    safe to answer is NOT that `FdDir` is nullary — it is that no
    modeled syscall can USE such an fd as a dirfd.  All five path-taking
    specs gate on `AT_FDCWD32` and decline everything else
    (`openat_body_spec`, `faccessat_body_spec`,
    `Fs.Namei.unlinkat_body_spec`, `Fs.Stat.readlinkat_spec`,
    `Fs.Stat.newfstatat_spec`), and nothing modeled moves the working
    directory or creates a directory (no chdir, fchdir, mkdirat,
    renameat or linkat).  If ANY of those gains a real-dirfd arm, then
    openat(fd_of_"..", "x") and openat(fd_of_".", "x") become
    distinguishable and this arm has to be revisited.

    ONE ANSWER IS ALREADY OBSERVABLE, and it is not this arm's doing:
    `Fs.Sync.fsync_spec` returns 0 for an `FdDir`, which is wrong on a
    filesystem whose directories carry no `.fsync`.  Answering ".."
    widened that divergence's precondition from "the cwd is on procfs or
    sysfs" to include a cwd whose PARENT is, which is a strictly larger
    set because a mount point's parent sits on another filesystem.

    ".." IS NOT `Fs.fs_lookup`-ABLE, and that is the point: without this
    arm the read shape would call it absent (-ENOENT, which Linux never
    returns for "..") and the create shape would MINT A KEY spelled "..". -/
def path_is_dirref (p : Fs.path) : Bool :=
  Fs.path_eqb p dot_path || Fs.path_eqb p dotdot_path

/-- Resolve an O_RDONLY open after pathname fetch and dirfd validation. -/
def openat_read_spec (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdDir))
  else
    match Fs.fs_lookup (m_fs m) p with
    | none => err_ret ENOENT
    | some _ =>
        open_result_spec m
          (fun fd => with_fds (fd_insert (m_fds m) fd
            (FdEntry.FdFile p (BitVec.ofInt 64 0))))

/- A name the flat map only IMPLIES is a directory: some key lives
    under it (`Fs.Namei.fs_under`).  On every write-create arm below it
    gets the answer a directory reference gets, and the test is written
    at each arm as `path_is_dirref p || fs_under (m_fs m) p` so that the
    directory the map implies and the directory reference the walk
    settles are answered by the same branch.

    THE DERIVATION IS THE ONE THE DOT ARMS ALREADY CARRY, with the
    dentry coming from a lookup instead of from `handle_dots`.
    `open_last_lookups` (fs/namei.c) takes the LAST_NORM branch and
    reaches the existing name by either of the routes that agree on what
    matters: `lookup_fast_for_open` returns a cached POSITIVE dentry
    (under O_CREAT it discards a negative one, and under O_CREAT|O_EXCL
    it returns nothing at all), and when it returns nothing
    `lookup_open` runs under the parent's inode lock and hands back the
    positive dentry it finds.  On either route `FMODE_CREATED` stays
    clear: the fast route never touches it, and `lookup_open` clears it
    on entry and sets it only on the create path.  `do_open` then runs
    its `open_flag & O_CREAT`
    block: first `(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)`
    is -EEXIST, then `d_is_dir(nd->path.dentry)` is -EISDIR, and both
    are returned BEFORE `may_open` and before any `O_TRUNC` handling.
    So an O_CREAT open of a directory answers -EEXIST under O_EXCL and
    -EISDIR without it, for every access mode the word carries.
    (`may_open`'s own `case S_IFDIR: if (acc_mode & MAY_WRITE) return
    -EISDIR` is the derivation for a write open WITHOUT O_CREAT, which
    no arm below is: every admitted write-create word carries O_CREAT.)
    All fs/namei.c, Linux v6.18.46; each function named was read at
    that version for this arm.

    WHY THIS IS AN ANSWER AND NOT A DECLINE.  A decline is for what the
    model cannot judge, and this it can: the answer is deterministic, it
    does not depend on which filesystem the directory is on, and it
    leaves the model unchanged, so the same image drives a source and a
    target into the same branch.  Without this arm the create shapes
    would MINT a key `a` beside `a/b` — a file system no directory tree
    can be — and a later `unlinkat` of that key would hit
    `Fs.Namei.fs_under` and decline a run that Linux had already
    answered.  `Fs.valid_fs` admits such an image (its keys are only
    sorted and NUL-free), so the divergence would be reachable on the
    plain binary of every whole-program example.
    This leaves three cases open: the NAME_MAX component, the read
    arm's -ENOENT for the same name, and the EMPTY real directory,
    which no `fs_under` can see.

    THE ANSWER IS DETERMINISTIC, with no `openat_errnos` alternative
    beside it, so it joins the arms `openat_body_spec`'s APPROXIMATION
    paragraph lists.  No modeled syscall makes a directory, so the
    `reject` twin that paragraph asks of each such arm is the one
    `Checks/Cases/Fs/Open.lean` carries:
    `Checks.Cases.Fs.Open.openat_implied_directory_create_eisdir` shows
    the offered descriptor refused beside the -EISDIR accepted, so this
    arm's twin is pinned there rather than in this module. -/

/-- Resolve the clobbering O_WRONLY|O_CREAT|O_TRUNC open shape.  A
    directory reference, or a name the map implies is a directory, is
    -EISDIR (`do_open`'s `d_is_dir`, above). -/
def openat_create_spec (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else create_wronly p m

/-- The file system after an APPEND open: unchanged when the path is
    already there, and carrying a new empty file when it is not.

    THE DIFFERENCE FROM `create_wronly` IS THE WHOLE POINT OF THE ARM.
    `build_open_flags` turns O_TRUNC into `op->open_flag`'s O_TRUNC and
    `do_open` (fs/namei.c) then calls `handle_truncate`, which empties an
    existing file; nothing on the O_APPEND path does, since O_APPEND is
    a file-STATUS flag `do_dentry_open` copies into `f_flags` and reads
    at write time (fs/open.c, mm/filemap.c `generic_write_checks`, Linux
    v6.18.46).  So an append open of an existing file must leave the
    bytes exactly where they were — writing them back through `fs_set`
    would be a no-op only for a sorted image, and this expresses the
    intent instead of leaning on that. -/
def append_open_fs (fs : Fs.Fs) (p : Fs.path) : Fs.Fs :=
  match Fs.fs_lookup fs p with
  | some _ => fs                        -- the file exists: O_APPEND never truncates
  | none => Fs.fs_set fs p []           -- O_CREAT mints it empty

/-- The effect a modeled APPEND write-open records: either an errno from
    `openat_errnos` (the same untracked environment conditions the other
    write-open shapes admit, this alternative also keeping the spec
    receptive when no free fd < 2^31 exists), or the lowest free fd bound
    to a `State.FdFileA` on `p`, with `p` created empty only if it was
    absent.

    THE OFFSET STARTS AT 0 AND THAT IS EXACT rather than a convenience.
    Linux gives every freshly opened description `f_pos = 0` —
    `alloc_empty_file` zeroes the `struct file` and no O_APPEND path
    assigns to `f_pos` at open time, which is why `fopen(p, "a")` has to
    be followed by an `ftell` that seeks to learn the size.  The append
    positioning happens per WRITE, in `generic_write_checks`, and
    `ReadWrite.write_spec`'s `FdFileA` arm is where the model records
    it.

    THE REGULAR-FILE PREMISE OF `create_wronly` IS SHARED, unchanged: `p`
    is an uninterpreted byte string, so a name Linux would resolve to a
    device, FIFO or kernfs attribute is recorded here as an ordinary
    file. -/
def open_append (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  alt (bind (errno_from openat_errnos) (fun e => err_ret e))  -- untracked env failure or no free fd
      (bind (lowest_fd (m_fds m)) (fun fd =>
        seqSpec (set_fs (append_open_fs (m_fs m) p))
          (seqSpec (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p (BitVec.ofInt 64 0))))
            (ret_only fd))))

/-- Resolve the APPEND write-create open shape.

    A DIRECTORY REFERENCE IS -EISDIR, the clobbering shape's answer and
    not the exclusive shape's -EEXIST, and the reason is which test
    `do_open` (fs/namei.c) reaches first.  With O_CREAT set it returns
    -EEXIST only under O_EXCL, which this word does not carry; the next
    test is `d_is_dir(nd->path.dentry)`, and that is -EISDIR.  So "." and
    ".." answer here exactly as they do for O_WRONLY|O_CREAT|O_TRUNC,
    ahead of `may_open`, and O_APPEND changes nothing about it.  An
    IMPLIED directory (`fs_under`) takes the same branch for the reason
    given above `openat_create_spec`: the dentry the lookup finds is
    positive and `d_is_dir`, and the word carries no O_EXCL. -/
def openat_append_spec (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else open_append p m

/-- Resolve an exclusive write-create open after pathname fetch.  A
    directory reference and an implied directory are -EEXIST, not
    -EISDIR: `do_open` tests O_EXCL against `FMODE_CREATED` before it
    tests `d_is_dir`, and a name that exists — as a key, as ".", or as
    the directory some key lives under — was not created (see above
    `openat_create_spec`). -/
def openat_excl_spec (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match Fs.fs_lookup (m_fs m) p with
    | some _ => err_ret EEXIST
    | none => create_wronly p m

/-- The effect a modeled READ-WRITE open records: either an errno from
    `openat_errnos`, or the lowest free fd bound to a `State.FdFileRW`
    on `p`, with the file system left as `fs'`.

    THE OFFSET STARTS AT 0 for both directions, and it is the same
    `f_pos` both use: `alloc_empty_file` (fs/file_table.c) zeroes the
    `struct file`, and nothing on the O_RDWR path assigns to `f_pos` at
    open time (Linux v6.18.46).  O_TRUNC does not move it either — it empties the file
    through `handle_truncate` and leaves the position alone, which is
    why a truncating open is `fs'` and not an offset.

    THE REGULAR-FILE PREMISE OF `create_wronly` IS SHARED, unchanged:
    `p` is an uninterpreted byte string, so a name Linux would resolve
    to a device, FIFO or kernfs attribute is recorded here as an
    ordinary file.
    This kind widens that premise's reach by one direction rather than
    by a new premise: a character device opened O_RDWR is readable AND
    writable in the model, where the other kinds open the same name one
    way at a time. -/
def open_rdwr (p : Fs.path) (fs' : Fs.Fs) (m : Model) : SysSpec SyscallEffect :=
  alt (bind (errno_from openat_errnos) (fun e => err_ret e))  -- untracked env failure or no free fd
      (bind (lowest_fd (m_fds m)) (fun fd =>
        seqSpec (set_fs fs')
          (seqSpec (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p (BitVec.ofInt 64 0))))
            (ret_only fd))))

/-- Resolve one of the four non-exclusive READ-WRITE open words, with
    `creat` and `trunc` the two bits that separate them
    (`rdwr_open_word` says why they are one arm).

    THE FOUR ANSWERS, all of them `do_open`'s (fs/namei.c, Linux
    v6.18.46) and none of them new to this file:

    - a DIRECTORY REFERENCE, or an IMPLIED directory (`fs_under`, see
      above `openat_create_spec`), is -EISDIR whatever the two bits say,
      and the two bit settings reach it at different sites.  With O_CREAT it
      is `do_open`'s own `d_is_dir(nd->path.dentry)`, inside the
      `open_flag & O_CREAT` block; without it, nothing in that block
      runs and the answer comes from `may_open`'s `case S_IFDIR:
      if (acc_mode & MAY_WRITE) return -EISDIR`, with MAY_WRITE present
      because `build_open_flags` (fs/open.c) sets
      `acc_mode = ACC_MODE(flags)` and `ACC_MODE` maps O_RDWR to
      MAY_READ|MAY_WRITE (include/linux/fs.h).  Same errno, two
      derivations, and the second is the one O_RDONLY never reaches —
      which is why the plain read arm hands "." a descriptor and this
      arm cannot.
    - an ABSENT name is a fresh empty file under O_CREAT and -ENOENT
      without it.  The -ENOENT is `lookup_open`'s negative dentry with
      no LOOKUP_CREATE, the same answer `openat_read_spec` gives.
    - an EXISTING file is emptied under O_TRUNC and keeps its bytes
      without it.  `do_open` arms `handle_truncate` on
      `d_is_reg(nd->path.dentry) && open_flag & O_TRUNC`; nothing else
      on this path touches the file's contents at open time.
    - a file the open just CREATED is empty either way, which is why
      `creat` and `trunc` do not have to be composed on that branch.
      Linux says the same thing rather than merely agreeing by
      arithmetic: `do_open` clears O_TRUNC from `open_flag` under
      `file->f_mode & FMODE_CREATED` before the truncate test, so a
      created file is never truncated at all. -/
def openat_rdwr_spec (creat trunc : Bool) (p : Fs.path) (m : Model)
    : SysSpec SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EISDIR
  else
    match Fs.fs_lookup (m_fs m) p with
    | none =>
        if creat then open_rdwr p (Fs.fs_set (m_fs m) p []) m
        else err_ret ENOENT
    | some _ =>
        open_rdwr p (if trunc then Fs.fs_set (m_fs m) p [] else m_fs m) m

/-- Resolve an exclusive READ-WRITE create open.  The shape of
    `openat_excl_spec` with the fd kind changed and no other
    difference: O_EXCL's -EEXIST is decided before any type test, so a
    directory reference or an implied directory answers -EEXIST here
    rather than the -EISDIR `openat_rdwr_spec` gives it. -/
def openat_rdwr_excl_spec (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  if path_is_dirref p || fs_under (m_fs m) p then err_ret EEXIST
  else
    match Fs.fs_lookup (m_fs m) p with
    | some _ => err_ret EEXIST
    | none => open_rdwr p (Fs.fs_set (m_fs m) p []) m

/-- Resolve an O_RDONLY|O_DIRECTORY open after pathname fetch.

    THE ARM EXISTS BECAUSE -ENOTDIR IS TYPE-BLIND.  `build_open_flags`
    (fs/open.c) turns O_DIRECTORY into LOOKUP_DIRECTORY, and `do_open`
    (fs/namei.c) answers -ENOTDIR for any resolved dentry that
    `d_can_lookup` (include/linux/dcache.h) refuses.  That test runs
    after the O_CREAT block and before both `may_open` (fs/namei.c) and
    `vfs_open` (fs/open.c).  So the model does NOT have to know which
    kind of non-directory a key names: a FIFO, a socket, a character
    device and a regular file all answer -ENOTDIR, and none of them gets
    as far as the file operations that would make them differ.  This is
    the one openat arm that does not rest on the model's regular-file
    premise.  Linux v6.18.46.

    THE ANSWERS.

    - "." and ".." are directories the walk settles out of itself
      (`path_is_dirref`), so LOOKUP_DIRECTORY is satisfied and the open
      succeeds with the same `FdDir` the plain read arm hands back.  The
      whole argument for answering ".." — and the condition that would
      falsify it — is on `path_is_dirref`; nothing here weakens it,
      because this arm mints exactly the entry that arm already mints.
    - a name the map HOLDS is a non-directory, hence -ENOTDIR.
    - a name the map does not hold does not resolve, hence -ENOENT, the
      same deterministic answer the read arm gives for it.

    BOTH OF THOSE ERRNOS ARE DETERMINISTIC, with no `openat_errnos`
    alternative beside them, so they join the arms
    `openat_body_spec`'s APPROXIMATION paragraph enumerates: a real
    kernel out of descriptors answers -EMFILE before path resolution
    reaches either, and this arm insists on the resolution errno.  That
    paragraph carries the argument and the cost; this is the pointer to
    it.

    TWO GUARDS THIS ARM TAKES THAT THE READ ARM CANNOT, and the
    asymmetry is deliberate rather than an oversight.  A single component
    over `Uapi.NAME_MAX` is the FILESYSTEM'S -ENAMETOOLONG, which a model
    with no filesystem type cannot pick; a name some key lives UNDER
    (`Fs.Namei.fs_under`) is an implied directory, where this arm would
    answer -ENOENT and Linux would hand back a directory fd.  Both are
    real gaps in the read arm too, and the NAME_MAX one in the
    write-create arms, and neither can be GUARDED there: `Examples.cp_ns` and
    `Examples.headcp_ns` reach those arms with argv-derived paths of
    length 256..4095, and a new `unmodeled` an example reaches makes its
    `Equivalence.strong_universal_T` FALSE rather than narrower.  No
    example can reach THIS arm — it is selected by a flag word every
    example's opens leave clear — so the guards are free here and are
    taken.
    `Fs.Open.faccessat_body_spec` carries the same two for the same
    reasons.  The write-create arms ANSWER the implied directory instead
    of guarding it (see above `openat_create_spec`): their answer is
    deterministic and image-independent where this arm's would be a
    directory fd the model has no path for.

    WHAT IS STILL NOT ANSWERED, and it is the case the flag is usually
    reached for: a directory named by a path with a separator in it.
    `openat_resolved_spec`'s hoisted guard declines that before any flag
    is looked at, so `openat(AT_FDCWD, "/usr/share/x", O_RDONLY |
    O_DIRECTORY)` is `unmodeled` and this arm never sees it.  The only
    directories a plain name can denote in a flat map are "." and "..".

    WHAT THE -ENOENT RESTS ON is the WORLD `faccessat_spec` states in
    full: every key is a regular file directly in the working directory
    and the working directory holds nothing else.  A real directory the
    map does not hold — an EMPTY one, which no `fs_under` can see —
    answers 0 on Linux and -ENOENT here.  That is the flat-namespace
    false rejection `openat` already has, not a new one: the read arm
    answers the same -ENOENT for the same name. -/
def openat_dir_spec (p : Fs.path) (m : Model) : SysSpec SyscallEffect :=
  if path_is_dirref p then
    open_result_spec m
      (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdDir))
  else if decide (NAME_MAX < p.length) then unmodeled
    -- the filesystem's own -ENAMETOOLONG, which no filesystem type here
    -- can supply
  else if fs_under (m_fs m) p then unmodeled
    -- p names an implied directory: Linux resolves it, the map cannot
  else
    match Fs.fs_lookup (m_fs m) p with
    | none => err_ret ENOENT
    | some _ => err_ret ENOTDIR   -- a key is never a directory

/- Dispatch a fetched, nonempty AT_FDCWD pathname by modeled flag shape. -/

/- THE ONE PATHNAME SHAPE `openat` CANNOT JUDGE: one with a separator
    in it.

    The interpreted file system is a FLAT map from whole byte strings to
    contents (`Fs`): it has no directory structure.  Without a walk the
    model cannot reach any of the answers a walk produces — the -ENOENT
    of a missing parent, the -ENOTDIR of a non-directory component, the
    -EISDIR of a trailing slash on a file — and it cannot tell that two
    spellings name one file.  Its flat key is not any of those answers,
    it is a fourth thing.  So it declines, using the guard
    `Fs.Namei.unlinkat_body_spec` and `faccessat_body_spec` below already
    carry; faccessat's own WORLD paragraph names openat as sharing the
    gap, and this closes openat's half of it.

    ".." IS NOT HERE, deliberately.  It has no separator and the model
    knows its answers exactly, so it is an ARM (`path_is_dirref` above)
    rather than a decline.  A decline is for what the model cannot
    judge.

    THE SEPARATOR-BEARING PATHS THAT ARE ANSWERED are the exceptions
    that state the rule.  "/etc/localtime" (`localtime_path`) answers
    -ENOENT under a declared assumption about the image: the
    model still cannot judge the path, what it has is a declaration
    about the environment, and the arm's comment says exactly what that
    declaration covers and what it does not.  "/dev/null"
    (`Uapi.devnull_path`) and "/dev/urandom" (`Uapi.urandom_path`) are
    DEVICES, whose every answer comes from a driver rather than from
    the file system, so the flat map's silence about directories costs
    nothing there.  `openat_sep_spec` is tested before the decline and
    dispatches all of them.
    WHAT IS NOT GUARDED HERE, and why this file's two syscalls differ.
    faccessat also declines a component over `NAME_MAX` and a name that
    `fs_under` shows is an implied directory.  Neither guard is added
    here because neither can be discharged in `Examples.cp_ns` and
    `Examples.headcp_ns`: their argv-derived paths range over lengths
    256..4095, and `Fs.valid_fs` permits an image whose keys live under
    an argv name.  Guarding either makes
    `Equivalence.strong_universal_T` FALSE for both examples rather than
    narrower, which is a different thing from the narrowing this guard
    does make (see `Run.valid_argv`).  The implied directory is instead
    ANSWERED on the write-create arms — a deterministic -EISDIR or
    -EEXIST that both examples' proofs carry as a lane of their own (see
    above `openat_create_spec`) — and stays a gap on the read arm, which
    answers -ENOENT where Linux opens the directory.  The `NAME_MAX`
    component cannot be answered on any arm: it is a property of the
    FILESYSTEM, not of fs/namei.c.  `link_path_walk` bounds nothing
    per-component; the -ENAMETOOLONG comes out of the filesystem's own
    `->lookup`: the EXT4_NAME_LEN test in `ext4_lookup` and
    `__ext4_find_entry`, fs/ext4/namei.c, and the NAME_MAX test in
    `simple_lookup`, fs/libfs.c (both Linux v6.18.46).  A model with no
    filesystem type that answered 255 would be inventing one, and would
    be wrong on a filesystem whose limit differs.

    DIRECTION.  This decline is for SOUNDNESS, not a coverage cost.
    Without it, the create shapes above would answer SUCCESS for every
    such path and mint a flat key for it: `openat(AT_FDCWD, "/no/such/file",
    O_WRONLY|O_CREAT|O_TRUNC, 0644)` would return an fd where Linux returns
    -ENOENT, and no `openat_errnos` alternative could rescue it, because
    neither ENOENT nor EISDIR is injectable.  That would be the model
    admitting a trace Linux refuses. -/

/-- A pathname the read and write-create arms above resolve on their own
    terms: not a directory reference, and not slash-bearing.  This is the
    premise the whole-program examples carry about their argv-derived
    paths; `Run.valid_argv`'s fifth clause is what supplies it.

    IT DOES NOT SAY WHETHER THE NAME IS AN IMPLIED DIRECTORY.  That is a
    fact about the image, not the path, so the write-create arms test
    `fs_under` beside it and the examples split on that test where they
    reach those arms: a plain name some key lives under is the -EISDIR
    lane, and a plain name nothing lives under is the create.

    IT IS NOT ENOUGH FOR `openat_dir_spec`, which is why that arm is not
    counted here: being plain does not get a name past that arm's
    `Uapi.NAME_MAX` and `Fs.Namei.fs_under` guards.  No example reaches
    it, so nothing needs it to. -/
def openat_plain_name (p : Fs.path) : Bool :=
  !(path_is_dirref p) && !(path_has_slash p)

theorem openat_plain_name_nodirref (p : Fs.path)
    (H : openat_plain_name p = true) : path_is_dirref p = false := by
  unfold openat_plain_name at H
  rw [Bool.and_eq_true] at H
  simpa using H.1

theorem openat_plain_name_noslash (p : Fs.path)
    (H : openat_plain_name p = true) : path_has_slash p = false := by
  unfold openat_plain_name at H
  rw [Bool.and_eq_true] at H
  simpa using H.2

/-- A directory reference has no separator, so the dot arms get past the
    guard from the same hypothesis that selects them. -/
theorem path_is_dirref_no_slash (p : Fs.path)
    (H : path_is_dirref p = true) : path_has_slash p = false := by
  unfold path_is_dirref at H
  rw [Bool.or_eq_true] at H
  rcases H with H | H
  · have hp : p = dot_path := (Fs.path_eqb_eq p dot_path).mp H
    rw [hp]
    decide
  · have hp : p = dotdot_path := (Fs.path_eqb_eq p dotdot_path).mp H
    rw [hp]
    decide

/-- "/etc/localtime", the file a C library's `tzset` opens to learn the
    local zone: musl 1.2.6 src/time/__tz.c, `do_tzset`, takes it when
    TZ is unset and hands it to src/time/__map_file.c, which opens
    it O_RDONLY|O_CLOEXEC|O_NONBLOCK; glibc's tzfile reader opens the
    same path.  It is the ONE absolute path this file answers, and the
    answer is -ENOENT.

    THIS IS A DECLARED ENVIRONMENT ASSUMPTION: an O_CREAT-free open of
    /etc/localtime answers -ENOENT in the image.  Spelled out, /etc is a
    directory, and the walk of /etc/localtime reaches no inode: either
    there is no entry, or there is a symlink whose own target walk
    answers -ENOENT.  A dangling symlink at /etc/localtime is INSIDE
    that premise — every admitted word lacks O_NOFOLLOW, so the trailing
    `step_into` follows it and the target's walk answers the same
    -ENOENT — and a regular file at /etc is OUTSIDE it, where
    `link_path_walk` answers -ENOTDIR and the model would be wrong
    rather than declined.  Nothing in the model derives the premise,
    and no `in_fs` a caller supplies can state it, because the flat map
    has no way to say "this absolute path is absent" any more than it
    can say "this name is a device".  It is an assumption about the
    environment every run is launched in, of the same kind as the
    "working directory holds nothing else" world `faccessat_spec`
    states, and it is written down here, at the arm that consumes it,
    so that a reader who changes the image knows what to revisit.

    WHAT IT BUYS.  A program that calls `localtime`, `ctime_r` or
    anything else that runs `tzset` opens this path before it does
    anything the model can see, often before `main`; with the separator
    decline alone that open would be `unmodeled` and the run would leave
    the modeled surface on its first timestamp.  For `tzset` a missing file
    is the ordinary case — the library falls back to UTC — so the
    -ENOENT is image-independent and needs no content model.

    THE KERNEL PATH.  Under a flag word WITHOUT O_CREAT the walk reaches
    the last component and finds no inode: `open_last_lookups`
    (fs/namei.c) takes the `lookup_fast_for_open` or `lookup_open`
    result, a negative dentry, into `step_into`, whose `handle_mounts`
    calls `traverse_mounts`, and that answers -ENOENT for a dentry
    `d_flags_negative` is true of (all fs/namei.c, Linux v6.18.46).
    This runs before `do_open`, so neither the O_DIRECTORY -ENOTDIR test
    nor `may_open` is reached, and the answer does not turn on the
    access mode: O_RDONLY, O_RDWR, O_RDWR|O_TRUNC and O_RDONLY|O_DIRECTORY
    are -ENOENT alike.

    THE ARM IS FLAG-BLIND, AND THAT IS SOUND ONLY BECAUSE OF THE ORDER.
    It tests the O_CREAT bit and nothing else; read alone it would
    answer -ENOENT to O_TMPFILE, where `build_open_flags` is -EINVAL
    before any walk, and to O_NOFOLLOW on a dangling link, where the
    answer is -ELOOP.  Neither reaches it: `openat_core_spec` refuses
    every flag word `modeled_open_flags` does not admit BEFORE the
    pathname is fetched, so the O_CREAT-free residues that arrive here
    are exactly O_RDONLY, O_RDONLY|O_DIRECTORY, O_RDWR and
    O_RDWR|O_TRUNC, the words the paragraph above answers for.  A
    widening of `modeled_open_flags` has to revisit this arm.

    WHAT IT DOES NOT COVER, each fail-closed rather than answered:

    - Any word WITH O_CREAT.  `lookup_open` (fs/namei.c) would create the
      file under /etc, a directory the model has no representation of
      and no parent to create anything in; answering success would mint
      a key the map cannot mean, which is the unsoundness the separator
      decline exists to prevent.
    - An image whose map HOLDS the key "/etc/localtime", or a key under
      it.  A program that ships a zoneinfo file in its image is opening
      a file the model has under that key, and the assumption does not
      hold for that image.  It is declined, not answered from the map,
      for the reason
      `Checks.Cases.Fs.Open.openat_slash_key_in_image_unmodeled`
      pins for every slash-bearing key: the map does not say whether the
      key is the absolute path or a working-directory name spelled with
      separators, so it cannot judge the open.  (And a key UNDER it makes
      the path a directory Linux would open where -ENOENT is wrong.)
      This guard is a courtesy to an `in_fs` that contradicts the
      premise, not part of the soundness argument: `Fs.valid_fs` admits
      a key spelled "etc/localtime" with the working directory at "/",
      which names the same file, and the arm answers -ENOENT over it.
      Under the premise no such key exists in any spelling.

    THE MATCH IS ON THE EXACT BYTE STRING.  "/etc//localtime",
    "/etc/./localtime" and "//etc/localtime" name the same file on Linux
    and are all declined here: the assumption was declared for one
    spelling, and the model has no walk to identify the others with
    it. -/
def localtime_path : Fs.path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 101, BitVec.ofInt 8 116, BitVec.ofInt 8 99,
   BitVec.ofInt 8 47, BitVec.ofInt 8 108, BitVec.ofInt 8 111, BitVec.ofInt 8 99,
   BitVec.ofInt 8 97, BitVec.ofInt 8 108, BitVec.ofInt 8 116, BitVec.ofInt 8 105,
   BitVec.ofInt 8 109, BitVec.ofInt 8 101]

def openat_localtime_spec (flags : word) (m : Model) : SysSpec SyscallEffect :=
  match Fs.fs_lookup (m_fs m) localtime_path with
  | some _ => unmodeled   -- the image ships the file: the assumption fails
  | none =>
      if fs_under (m_fs m) localtime_path then unmodeled  -- ...or a directory there
      else if flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT
      then unmodeled      -- Linux would create it; the model has no /etc
      else err_ret ENOENT

/- "/dev/null", the one DEVICE this file answers, and the descriptor
    kind `State.FdDevNull` it mints.

    THE ENVIRONMENT ASSUMPTION, stated here and consumed by every arm
    that answers for the kind: the image's /dev/null is the null
    device, character major 1 minor 3, whose operations are
    `null_fops` (drivers/char/mem.c, Linux v6.18.46).  That is what the
    name means on every Linux system — `devlist[3]` is "null" and
    devtmpfs, or the container runtime, creates the node from it — and
    it is the reason the arm is SOUND without a filesystem: nothing
    Linux does through this descriptor depends on the image, because
    `null_fops` never touches a page, a buffer or an inode's contents.
    The assumption does NOT reach an image whose map holds the key
    "/dev/null" or a key under it; that image is declined.  The guard
    on the map is a courtesy to a contradicting `in_fs`, not part of
    the soundness argument.

    THE KERNEL PATH the flag words take, all fs/namei.c v6.18.46 and
    all decided before the device's own `open` runs:

    - O_RDONLY, and the READ-WRITE words without O_EXCL: `do_open`
      reaches `may_open`, whose S_IFCHR arm passes
      (`may_open_dev` is the one thing it tests, and -EACCES from it is
      already an `openat_errnos` alternative), then `vfs_open` ->
      `do_dentry_open` (fs/open.c) -> `chrdev_open` (fs/char_dev.c)
      -> `memory_open` (drivers/char/mem.c), which installs
      `null_fops`.  The descriptor carries the access mode
      `do_dentry_open` set: FMODE_READ, FMODE_WRITE or both.
    - O_WRONLY|O_CREAT|O_TRUNC: the same, because O_CREAT on an
      existing name creates nothing — `lookup_open` finds the positive
      dentry and `FMODE_CREATED` stays clear — and `do_open` arms
      `handle_truncate` only under `d_is_reg(nd->path.dentry)`, which a
      character device fails, so the O_TRUNC is inert.
    - O_WRONLY|O_CREAT|O_APPEND: the same again.  O_APPEND reaches
      `f_flags` and nothing in `null_fops` reads it: `write_null` and
      `write_iter_null` return the count without consulting a position
      (mem.c's own comment on `null_lseek` says fopen with "a" is the
      point), and no modeled arm on this kind reads `f_flags`
      (`Fcntl.getfl_f_flags` and `Fcntl.setfl_noop_on` both decline it),
      so the append word mints the same write-only entry the clobbering
      word does.  That is exactly the O_APPEND-is-unobservable argument
      `State.FdFileA` exists because a REGULAR file breaks; here it
      holds.
    - O_CREAT|O_EXCL, in either access mode: `do_open`'s
      `(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)` is
      -EEXIST, before `may_open` — deterministic, as on every existing
      name.
    - O_RDONLY|O_DIRECTORY: `do_open`'s `(nd->flags & LOOKUP_DIRECTORY)
      && !d_can_lookup(...)` is -ENOTDIR; `openat_dir_spec` carries the
      same argument for a plain name.

    THE MATCH IS ON THE EXACT BYTE STRING, as for every answered
    absolute path: "/dev//null" and "/dev/./null" stay declined.

    WHY A DEVICE AND NOT A FILE.  If this name were a key, a read would
    hand back bytes a write had recorded, where `read_null` returns
    0.  `State.FdDevNull` carries no path and no contents, so no arm can
    make that mistake; each answers from `null_fops` or declines.

    The byte string itself is `Uapi.devnull_path`, shared with
    `Fs.Stat.fstat_devnull_spec`. -/

/-- The success shape every admitted word shares: the injectable errno,
    or the lowest free fd bound to the entry with the granted mode. -/
def open_devnull (m : Model) (rd wr : Bool) : SysSpec SyscallEffect :=
  open_result_spec m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdEntry.FdDevNull rd wr)))

def openat_devnull_spec (flags : word) (m : Model) : SysSpec SyscallEffect :=
  match Fs.fs_lookup (m_fs m) devnull_path with
  | some _ => unmodeled   -- the image ships a FILE under the name: outside the assumption
  | none =>
      if fs_under (m_fs m) devnull_path then unmodeled  -- ...or a directory there
      else
      let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
      if fl == 0 then open_devnull m true false
      else if fl == wr_create_flags then open_devnull m false true
      else if is_excl_create fl then err_ret EEXIST
      else if fl == O_DIRECTORY then err_ret ENOTDIR
      else if fl == append_create_flags then open_devnull m false true
      else if rdwr_open_word fl then open_devnull m true true
      else if is_rdwr_excl_create fl then err_ret EEXIST
      else unmodeled   -- unreachable: `modeled_open_flags` admitted the word

/- "/dev/urandom", the second DEVICE this file answers, and the
    descriptor kind `State.FdUrandom` it mints.

    THE ENVIRONMENT ASSUMPTION, stated here and consumed by every arm
    that answers for the kind: the image's /dev/urandom is the random
    device, character major 1 minor 9, whose operations are
    `urandom_fops` (drivers/char/random.c, Linux v6.18.46) —
    `devlist[9]` is "urandom" (drivers/char/mem.c) and devtmpfs, or the
    container runtime, creates the node from it.  The assumption does
    NOT reach an image whose map holds the key "/dev/urandom" or a key
    under it; that image is declined.

    WHAT THE BYTES ARE.  Not a choice: the run's `State.in_urandom`
    declares them, in order, and `ReadWrite.read_urandom` hands them
    out from the front.  So /dev/urandom is an ARBITRARY BUT FIXED
    stream, a parameter of the
    execution like argv and envp, the same stream on both sides of an
    equivalence — and it is what makes a program that seeds itself from
    the device provable at all: every equivalence is proved for every
    stream, and no statement quantifies over the generator.
    `getrandom` (278) is deliberately NOT drawn from it; the two stay
    unrelated in the model.

    THE KERNEL PATH the flag words take, all fs/namei.c v6.18.46 and
    all decided before the device's own `open` runs:

    - O_RDONLY: `do_open` reaches `may_open`, whose S_IFCHR arm passes
      (`may_open_dev` is the one thing it tests, and -EACCES from it is
      already an `openat_errnos` alternative), then `vfs_open` ->
      `do_dentry_open` (fs/open.c) -> `chrdev_open` (fs/char_dev.c) ->
      `memory_open` (drivers/char/mem.c), which installs
      `urandom_fops`.  The descriptor carries FMODE_READ, FMODE_PREAD
      and FMODE_LSEEK (`do_dentry_open` sets the latter two and
      `memory_open` clears nothing).
    - O_CREAT|O_EXCL, in either access mode: `do_open`'s
      `(open_flag & O_EXCL) && !(file->f_mode & FMODE_CREATED)` is
      -EEXIST, before `may_open` — deterministic, as on every existing
      name.
    - O_RDONLY|O_DIRECTORY: `do_open`'s `(nd->flags & LOOKUP_DIRECTORY)
      && !d_can_lookup(...)` is -ENOTDIR.
    - THE WRITE WORDS ARE DECLINED, not answered: O_WRONLY and O_RDWR,
      with or without O_CREAT, O_TRUNC and O_APPEND.  Linux admits them
      — `may_open` passes, `may_open`'s `flag &= ~O_TRUNC` drops the
      truncation, and a write through the descriptor reaches
      `random_write_iter`, which mixes the bytes into the input pool
      (`write_pool_user`) and returns the count — and the model does
      not model writes into the pool, nor a descriptor on this device
      that could carry them.  A program that opens the device for
      writing leaves the modeled surface at the open.

    THE MATCH IS ON THE EXACT BYTE STRING, as for every answered
    absolute path: "/dev//urandom" and "/dev/./urandom" stay declined,
    and so does "/dev/random", which is a different device
    (`random_fops` blocks until the pool is ready).

    The byte string itself is `Uapi.urandom_path`, shared with
    `Fs.Stat.fstat_urandom_spec`. -/

/-- The success shape: the injectable errno, or the lowest free fd
    bound to the read-only entry. -/
def open_urandom (m : Model) : SysSpec SyscallEffect :=
  open_result_spec m
    (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdUrandom))

def openat_urandom_spec (flags : word) (m : Model) : SysSpec SyscallEffect :=
  match Fs.fs_lookup (m_fs m) urandom_path with
  | some _ => unmodeled   -- the image ships a FILE under the name: outside the assumption
  | none =>
      if fs_under (m_fs m) urandom_path then unmodeled  -- ...or a directory there
      else
      let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
      if fl == 0 then open_urandom m
      else if is_excl_create fl then err_ret EEXIST
      else if fl == O_DIRECTORY then err_ret ENOTDIR
      else if is_rdwr_excl_create fl then err_ret EEXIST
      else unmodeled   -- the write words (`wr_create_flags`,
                       -- `append_create_flags`, `rdwr_open_word`):
                       -- admitted by Linux into the pool, declined here

/-- "/tmp/<name>", the run's own PRIVATE temporary directory: the third
    absolute shape this file answers for, and the first that is a
    FILE rather than a device.

    THE ENVIRONMENT ASSUMPTION, stated here and consumed by the two
    arms below and by `Fs.Namei.unlinkat_tmp_spec`: /tmp is a distinct,
    WRITABLE directory PRIVATE to this run.  What that buys is the only
    thing the flat map needs — that the run's own table is the whole
    truth about the directory.  What the run holds there is
    `State.in_tmp`, the environment's declaration, plus what
    `create_wronly` created, minus what `Fs.Namei.unlinkat_spec`
    removed, and nothing outside the run can add a name or take one
    away between two of its syscalls.  Without privacy a second process
    could create the name between the run's own -ENOENT and its create,
    and the model would be answering about a directory it does not
    have.

    THE NAME IS AN INPUT, not a choice: `State.in_tmp` is arbitrary but
    fixed, a parameter of the execution as argv and envp are, and the
    SAME directory is seen by the source and the target of a pair, so
    every equivalence is proved for every declared /tmp.
    `State.fs_seed_tmp` seeds it into the initial file system under the
    absolute keys this arm reads, which is why read, write, lseek,
    fstat, fsync and close on the descriptor are the EXISTING
    `FdFile`/`FdFileW` arms, untouched: nothing here mints a new
    descriptor kind.

    THE THREE SHAPES ANSWERED, and only these:

    - O_WRONLY|O_CREAT|O_TRUNC of "/tmp/<name>" goes to
      `openat_create_spec`, which is what the plain arm does for a name
      in the working directory — the same arm, so the -EISDIR it
      answers for a directory the map implies is answered here too (see
      THE IMPLIED DIRECTORY below).  The mode argument is ignored there
      as it is here.
    - O_RDONLY of a "/tmp/<name>" whose key the run HOLDS goes to
      `openat_read_spec`.
    - the removal is `Fs.Namei.unlinkat_spec`'s arm.

    EACH FLAG WORD IS MATCHED PAST THE FILE'S SHARED IGNORED MASK,
    `open_ignored_flags`, and not past O_CLOEXEC alone: the mask is
    O_CLOEXEC, O_LARGEFILE and O_NONBLOCK, and `Z.ldiff` strips all
    three before the test, exactly as every other arm in this file does.
    So O_RDONLY|O_NONBLOCK and O_RDONLY|O_LARGEFILE reach the read arm
    and the create word reaches the create arm with any of the three
    set.  All three are inert on a regular file — O_CLOEXEC is a
    descriptor-table flag the model does not record, O_LARGEFILE is
    unconditional on a 64-bit ABI, and O_NONBLOCK on a regular file
    changes no answer any modeled operation gives — which is the
    argument the mask's own definition carries and the reason this arm
    does not narrow it.

    Every other word is DECLINED rather than answered: O_RDWR in either
    creating shape, O_APPEND, the O_EXCL words, O_DIRECTORY, and plain
    O_RDONLY of a name the run does not hold.  Linux answers all of
    them, and the model could derive several; this arm answers only
    the three shapes above and declines the rest, which is the narrower
    choice at every one of them.  A read of
    a name not held is the one worth naming twice: -ENOENT would follow
    from the privacy premise, and the decline is a choice, not a
    gap in the derivation.

    THE ONE GUARD AHEAD OF THE FLAG TEST.

    `Uapi.NAME_MAX` is the FILESYSTEM's own -ENAMETOOLONG, which
    fs/namei.c does not produce and a model with no filesystem type
    cannot invent (see `openat_plain_name`'s note, which explains why
    the plain arms cannot afford this guard and this one can: no
    example's argv reaches a /tmp path).

    THE IMPLIED DIRECTORY IS ANSWERED ON THE CREATE WORD AND DECLINED
    ON THE READ WORD, which is why `Fs.Namei.fs_under` is tested inside
    each word instead of ahead of both.  The declaration may name
    "a/b", and then "/tmp/a" is a DIRECTORY in the run's own /tmp: the
    flat map holds no directory, but a key living under the path is
    what says one is there, and that is the reading
    `openat_create_spec` already makes of a working-directory name.
    The two words part company because what Linux answers costs the
    model different things:

    - the create word IS `openat_create_spec`, reached here rather than
      restated, so the /tmp arm and the working-directory arm cannot
      drift apart.  A name the map implies is a directory answers
      `do_open`'s deterministic -EISDIR, taken under O_CREAT without
      O_EXCL and before `may_open` ever runs; the derivation, and why
      an ANSWER rather than a decline is the faithful choice, is
      written out above `openat_create_spec` and none of it is special
      to the working directory.  `path_is_dirref` is inert on this arm
      — `tmp_name` admits only a path beginning "/tmp/" and refuses "."
      and ".." — and sharing the arm anyway costs a test that cannot
      fire and buys a restatement that cannot rot.
    - the read word DECLINES it, which is a choice and
      not a gap in the derivation: answering means handing back a
      DIRECTORY DESCRIPTOR, and the model has no directory semantics to
      hand one out of.  That is the same trade the working-directory
      read arm makes.  The test stays
      inside the read branch rather than being dropped, because
      `Fs.valid_fs` admits an image holding "/tmp/a" and "/tmp/a/b" at
      once, and without it the lookup would hand out an `FdFile` on a
      name reality makes a directory. -/
def openat_tmp_spec (n p : Fs.path) (flags : word) (m : Model)
    : SysSpec SyscallEffect :=
  if decide (NAME_MAX < n.length) then unmodeled
  else
  let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
  if fl == 0 then
    (if fs_under (m_fs m) p then unmodeled  -- a directory descriptor: deferred
     else match Fs.fs_lookup (m_fs m) p with
          | none => unmodeled     -- a key the run does not hold
          | some _ => openat_read_spec p m)
  else if fl == wr_create_flags then openat_create_spec p m
  else unmodeled   -- every other word: see the comment above

/-- The pathnames with a separator that are ANSWERED, tested ahead of
    the separator decline.  Only a path with a separator can match, so
    the dispatch sits inside the true branch of `path_has_slash` in
    `openat_resolved_spec`: same answers as testing them first, and the
    slash-free arms and every proof that unfolds them are untouched.
    A path with a separator that no arm here names is the decline the
    paragraph above this one argues for. -/
def openat_sep_spec (p : Fs.path) (flags : word) (m : Model)
    : SysSpec SyscallEffect :=
  if Fs.path_eqb p localtime_path then openat_localtime_spec flags m
  else if Fs.path_eqb p devnull_path then openat_devnull_spec flags m
  else if Fs.path_eqb p urandom_path then openat_urandom_spec flags m
  else match tmp_name p with
       | some n => openat_tmp_spec n p flags m
       | none => unmodeled

/-- ORDER.  The guard is hoisted above the flag test rather than
    repeated inside each arm, and what makes that safe is a reachability
    fact about this file rather than an argument about Linux:
    `openat_core_spec` has ALREADY refused every flag word the model
    does not interpret, through `modeled_open_flags`, before this
    definition is reached.  So the `else unmodeled` below is
    unreachable, both orders answer `unmodeled` on exactly the same
    inputs, and hoisting changes no answer the model gives — only which
    of two reasons it declines for.  The kernel's order agrees, which is
    why the hoisted position is also the faithful one:  The walk that cannot be
    modeled precedes the flag-dependent decision in Linux too
    (`link_path_walk` runs before `may_open`'s -EISDIR), so the hoisted
    position is the faithful one.

    THE ARMS ARE NOT ALL TOTAL.  All but one answer every
    pathname they are handed; `openat_dir_spec` does not, and its
    declines are on the path rather than on the flag word.  The FINAL
    `else unmodeled` here is still unreachable — the branches
    exhaust what `modeled_open_flags` admits — but this dispatcher does
    not decline only above an arm: it also declines inside one, and the
    `Checks` mirror carries a matching decline inside
    `check_openat_dir`. -/
def openat_resolved_spec (p : Fs.path) (flags : word) (m : Model)
    : SysSpec SyscallEffect :=
  if path_has_slash p then openat_sep_spec p flags m else
  let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
  if fl == 0 then openat_read_spec p m
  else if fl == wr_create_flags then openat_create_spec p m
  else if is_excl_create fl then openat_excl_spec p m
  else if fl == O_DIRECTORY then openat_dir_spec p m
  else if fl == append_create_flags then openat_append_spec p m
  else if rdwr_open_word fl then
    openat_rdwr_spec (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p m
  else if is_rdwr_excl_create fl then openat_rdwr_excl_spec p m
  else unmodeled

/-- `openat dirfd path flags mode`.  Modeled shapes (the
    `open_ignored_flags` bits are accepted and ignored in all; `mode` is
    ignored):

    - O_RDONLY: open an existing file for reading (-ENOENT if absent),
      or a directory reference ("." or "..", `path_is_dirref`) for a
      directory fd (read on it is -EISDIR; see `FdEntry`);
    - O_WRONLY|O_CREAT|O_TRUNC: create or truncate, then write
      (-EISDIR on a directory reference, and on a name the map implies
      is a directory because some key lives under it — a directory
      cannot be opened for writing; `openat_create_spec` carries the
      derivation);
    - O_WRONLY|O_CREAT|O_EXCL (with or without O_TRUNC,
      `is_excl_create`): create, then write, but only if the path does
      NOT already exist — otherwise the deterministic real -EEXIST.
      The existence test comes BEFORE any type test, as Linux's does
      (fs/namei.c: O_EXCL on a positive dentry is -EEXIST whatever the
      dentry is), so a directory reference ("." or "..") and an implied
      directory are -EEXIST here, NOT the -EISDIR of the clobbering
      shape.
    - O_RDONLY|O_DIRECTORY: a directory reference gives the same `FdDir`
      the plain read shape gives it, a name the map holds gives
      -ENOTDIR, and a name it does not hold gives -ENOENT.  This is the
      only arm that declines on the PATH rather than only on the flags:
      it refuses a component over `Uapi.NAME_MAX` and a name some key
      lives under, which the read arm cannot and the write-create arms
      answer instead (`openat_dir_spec` says why the asymmetry is
      deliberate).
    - O_WRONLY|O_CREAT|O_APPEND (`append_create_flags`): open for
      writing, creating the file empty if it is absent and leaving an
      existing file's bytes ALONE, with every write through the fd
      landing at the then-current end of file (-EISDIR on a directory
      reference or an implied directory, the clobbering shape's answer —
      see `openat_append_spec`).  The fd is a `State.FdFileA`, a different
      kind from the other two write shapes' `State.FdFileW`; what turns
      on that is set out at `append_create_flags`.
    - the READ-WRITE words: O_RDWR alone, O_RDWR beside O_CREAT and/or
      O_TRUNC (`rdwr_open_word`), and O_RDWR|O_CREAT|O_EXCL with or
      without O_TRUNC (`is_rdwr_excl_create`).  The fd is a
      `State.FdFileRW`, the one kind that answers in BOTH directions
      off one `f_pos`; `openat_rdwr_spec` carries the table of what the
      O_CREAT and O_TRUNC bits each decide, and
      `openat_rdwr_excl_spec` the -EEXIST that separates the exclusive
      words from them.

    ALL OF THEM ARE ON A PATHNAME WITH NO SEPARATOR IN IT.  One with a
    separator is declined ahead of the flag test and reaches none of the
    arms above — see the guard in `openat_resolved_spec`, which also
    says what the create shapes would answer for such a path without it
    and why that is unsound — with the exceptions `openat_sep_spec` names:
    "/etc/localtime" is -ENOENT without O_CREAT, on a declared
    assumption about the image, and fails closed with it; "/dev/null"
    opens under every admitted access mode as a `State.FdDevNull`,
    -EEXIST under O_EXCL and -ENOTDIR under O_DIRECTORY, on the
    assumption `openat_devnull_spec` states; "/dev/urandom" opens
    read-only as a `State.FdUrandom`, with the same -EEXIST and
    -ENOTDIR, and declines the write words, on the assumption
    `openat_urandom_spec` states.  So "create" below always
    means "create the
    single-component name the program passed", never a name in a
    directory the model cannot see.  ".." is not declined: it is a
    directory reference and takes the same arm "." does
    (`path_is_dirref`).

    The EMPTY pathname always fails with -ENOENT, whatever the (modeled)
    flags (path_resolution(7); AT_EMPTY_PATH is not modeled) — in
    particular it never matches an empty-path key in the file-system
    image.

    ORDER.  The kernel's own order is `build_open_flags()`, then
    `getname()`, then `path_init`'s `fdget_raw` on the dirfd, and this
    spec follows it: a flag word the model does not interpret is
    unmodeled and yields `unmodeled` BEFORE any pathname is fetched (the kernel
    would never reach the pathname for a combination it rejects), while
    an over-long or unmapped path answers a real errno even when the
    dirfd is one the model declines.

    `dirfd` arrives already truncated to 32 bits (see `Syscall.fd32`), as
    openat declares it `int`: AT_FDCWD is recognized in the low half
    (`AT_FDCWD32`), so `openat(2^32 - 100, ...)` is AT_FDCWD.

    The pathname fetch has all three of `getname()`'s answers:
    -ENAMETOOLONG for a path with no NUL within PATH_MAX, -EFAULT for
    one with an unmapped byte, and the string itself otherwise.  Both
    failures are deterministic returns the model tracks, like -ENOENT —
    not injectable, so they are not in `openat_errnos`.

    Anything else — a dirfd other than AT_FDCWD, other flag
    combinations — is unmodeled: `unmodeled`.  An open on an arm that can
    SUCCEED may instead fail with an errno from `openat_errnos`
    (environment conditions the model does not decide; this alternative
    also keeps the spec receptive when no free fd < 2^31 exists).  The
    -EMFILE among them is the one that is not purely an
    environment condition: the model holds the run's soft RLIMIT_NOFILE
    in `State.m_nofile`, but `File.lowest_fd` ignores it,
    so this spec can hand out an fd Linux would have refused.  On
    success the kernel returns the lowest free fd (`File.lowest_fd`), as Linux
    does.  Flag arithmetic happens in `Int` on the unsigned flag word.

    APPROXIMATION (deliberate, and shared by every arm that reports a
    PATH-RESOLUTION errno deterministically — the empty-path and
    absent-file -ENOENT, the "." -EISDIR, the O_EXCL -EEXIST, the
    implied directory's -EISDIR and -EEXIST on the write-create arms
    (whose `reject` twin is
    `Checks.Cases.Fs.Open.openat_implied_directory_create_eisdir`),
    `openat_dir_spec`'s own pair, the -ENOTDIR for a name the map holds
    beside the -ENOENT for one it does not, and
    `openat_localtime_spec`'s -ENOENT, whose `reject` twin is
    `Checks.Cases.Fs.Open.openat_localtime_enoent` — both twins now
    landed in `Checks/Cases/Fs/Open.lean`): those
    arms admit that ONE answer and no `openat_errnos` alternative,
    whereas Linux can fail an openat with an errno raised BEFORE path
    resolution — `do_sys_openat2` calls `get_unused_fd_flags` before
    `do_filp_open`, so at RLIMIT_NOFILE the real call answers -EMFILE (or
    -ENFILE at the system limit) where the model insists on the
    resolution errno.  Errnos the kernel can raise before path resolution
    are OUTSIDE the modeled resolutions.  (The -ENAMETOOLONG and -EFAULT
    arms are NOT approximate in this way: `getname()` runs before
    `get_unused_fd_flags`, so those really do preempt fd exhaustion.)
    THE LIST IS HAND-MAINTAINED.
    This narrows the spec rather than widening it, so it admits nothing
    unsound; the cost is that a source and a target which diverge only
    under fd-table exhaustion are not distinguished by the proved
    theorem. -/
def openat_body_spec (i : SyscallInput) (m : Model)
    (dirfd pathp flags : word) : SysSpec SyscallEffect :=
  match read_cstr (i.in_mem) pathp with
    | .CstrTooLong => err_ret ENAMETOOLONG        -- no NUL within PATH_MAX
    | .CstrFault => err_ret EFAULT                -- unmapped byte in the path string
    | .CstrOk p =>
        if Fs.path_eqb p [] then err_ret ENOENT   -- empty pathname: always a real -ENOENT on Linux
        -- only now the dirfd (`path_init`'s `fdget_raw` runs after
        -- `getname`): the relative-to-a-dirfd modes aren't modeled, so we
        -- can't judge the call — `unmodeled`, NOT the program faulting.
        else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
        else openat_resolved_spec p flags m

def openat_core_spec (dirfd pathp flags : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
  -- `build_open_flags()` first, as Linux does: a flag combination the
  -- model does not interpret is unmodeled, so we can't judge the call —
  -- `unmodeled`, and in particular NOT one of the pathname errnos below,
  -- which the kernel would never reach for a combination it rejects.
  if !(modeled_open_flags flags) then unmodeled
  else
    -- then `getname()`: all three of its answers are real errnos.
    openat_body_spec i m dirfd pathp flags

def openat_spec (dirfd pathp flags : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  record_copyins [(pathp, cstr_access_len_aux (i.in_mem) pathp path_max)]
    (openat_core_spec dirfd pathp flags)

/-- `close fd`: 0 on a live fd (which is removed), -EBADF otherwise.
    `fd` arrives already truncated to 32 bits (see `Syscall.fd32`), so
    `close(2^32)` closes stdin.

    THE ARM IS KIND-BLIND ON PURPOSE, AND FOR A PIPE THAT IS
    LOAD-BEARING.  Removing the fd is the whole of what `pipe_release`
    does that a program can observe (fs/pipe.c:725-746, v6.18.46): it
    decrements `pipe->readers` or `pipe->writers` by the file's `f_mode`
    (:730-733), and the model reads that same fact back off the fd table
    (`State.pipe_end_live`) instead of keeping a counter.  So closing the
    last WRITE end is exactly what turns a
    later read of the drained pipe from a block into end-of-file, and
    closing the last READ end is what makes a later write a SIGPIPE the
    model declines — both without a line of pipe-specific code here.
    Buffered bytes are NOT dropped: the `m_pipes` entry stays (see
    `State.pipe_new_id`), and a reader whose end is still open still
    sees them, as it does on Linux. -/
def close_spec (fd : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some _ => seqSpec (set_fds (fd_remove (m_fds m) fd)) (ret_only (BitVec.ofInt 64 0))

/- The region a GROWING `ftruncate` must zero-fill is one the model can
    represent.  The endpoint measured is the NEW LENGTH itself, and the
    comparison is `ReadWrite.modeled_zero_fill`'s — the same one `ReadWrite.modeled_file_gap`
    makes of a write's offset, for the same reason: Linux extends a file
    into a HOLE for free, while the model holds the file as a flat byte
    list and has to build the zeros (`Fs.file_truncate`).

    A SHRINK is always judged — for `len` at or below the current length
    the subtraction is negative, so the comparison holds outright.  Note
    what that does and does not buy: the bound is ONE-SIDED, an upper
    bound on `len`, so it bounds `word_to_nat len` by
    `length data + rw_bytes_max` in BOTH directions.  A shrink is never
    free — `Fs.file_truncate` still builds `word_to_nat len` for its
    `repeat` argument, a unary numeral the size of the new length — it is
    merely never DECLINED. -/

/-- PORT SHIM: `Fs.ReadWrite.modeled_zero_fill`, copied here.  The same
    definition is in `Sys/Fs/ReadWrite.lean`, under the same name; this
    copy should be deleted in favour of the import. -/
def modeled_zero_fill (endpoint : Int) (data : List byte) : Bool :=
  decide (endpoint - (data.length : Int) ≤ Uaccess.rw_bytes_max)

def modeled_truncate_gap (data : List byte) (len : word) : Bool :=
  modeled_zero_fill (len.toNat : Int) data

/- ONE ARM FOR TWO KINDS.  `do_ftruncate`'s test is
    `!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)`
    (fs/open.c, Linux v6.18.46), and an O_RDWR description passes
    both halves exactly as an O_WRONLY one does; nothing further
    down reads the access mode.  The read-only `FdFile` arm above
    is the -EINVAL half of that same test.

     The arm is written once with an or-pattern
    (`| Some (FdFileW p _) | Some (FdFileRW p _) => ...`); Lean has no
    or-patterns, so the shared body is this definition and the two arms
    of `ftruncate_spec` call it.  Same term, one unfolding further out. -/
def ftruncate_file_arm (p : Fs.path) (len : word) (m : Model) : SysSpec SyscallEffect :=
  match Fs.fs_lookup (m_fs m) p with
  | none => unmodeled                        -- a writable file fd always points into the fs; see openat
  | some data =>
      if !(modeled_truncate_gap data len) then unmodeled
        -- a zero-fill too large to build as a byte list; Linux makes
        -- the file sparse for free — see `modeled_truncate_gap`
      else
        seqSpec (set_fs (Fs.fs_set (m_fs m) p (Fs.file_truncate data len)))
          (ret_only (BitVec.ofInt 64 0))
        -- NO set_fds: the offset is untouched, see the header

/-- `ftruncate fd len` (riscv64 nr 46, `SYSCALL_DEFINE2`).  Sets the
    file's length to exactly `len`: a shrink drops the tail, a grow
    zero-fills (`Fs.file_truncate`).

    THE FD'S OFFSET IS NOT TOUCHED, and that is the fact this spec most
    has to get right.  Linux resolves the descriptor with `fdget`, not
    `fdget_pos` — it does not even take the `f_pos` lock, and no
    assignment to `f_pos` exists anywhere on the path
    (`do_sys_ftruncate` -> `do_ftruncate` -> `do_truncate` ->
    `notify_change`, fs/open.c and fs/attr.c).  Contrast `ksys_write`
    (fs/read_write.c, Linux v6.1 through v6.12), which takes `fdget_pos`
    and writes the field back explicitly.  So a shrink can leave the
    offset PAST end-of-file, and the following write then re-grows the
    file with a hole in between — exactly what `Fs.file_write` already
    does for an lseek past the end.

    CHECK ORDER, from the kernel and not from the man page (fs/open.c;
    `inode_newsize_ok` in fs/attr.c is byte-identical across MAINLINE
    v6.1 through v6.12 — stable branches were not separately audited, so
    read every window here as mainline — and the entry point's only
    CHECK-ORDER changes in it
    are a Landlock hook swap, the v6.9 split of `do_ftruncate` out of
    `do_sys_ftruncate`, and the v6.10 `unsigned long` -> `off_t`
    parameter retype, which is compat-only and changes nothing on a
    64-bit ABI):

    - `len` NEGATIVE as a signed 64-bit value is -EINVAL, and it is
      decided BEFORE THE FD IS LOOKED UP: `do_sys_ftruncate` tests
      `length < 0` ahead of its `fdget`.  So `ftruncate(-1, -1)` is
      -EINVAL, not -EBADF — the ordering a spec written from the man
      page gets backwards;
    - an fd that is not open is -EBADF;
    - a channel, EITHER END OF A PIPE, a socket, a read-only file fd, or
      a directory fd is -EINVAL.  One kernel condition covers all five,
      `!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)`, so a
      directory is -EINVAL and NOT -EISDIR (that errno belongs to
      `vfs_truncate`, which only the path-based truncate(2) reaches) and
      a pipe is -EINVAL and NOT -ESPIPE (an lseek errno that appears
      nowhere in this path).  A channel answers -EINVAL whichever HALF
      of that condition it fails: /dev/null and a pipe are not S_ISREG,
      and a REGULAR file opened O_RDONLY fails on FMODE_WRITE instead.
      What this arm therefore assumes of the
      environment is the disjunction, not the pipe: no channel the model
      is handed is a writable regular file.  Nothing enforces that.

      THE WRITE END IS THE CASE WORTH SEPARATING OUT, because it is the
      one an access-mode reading of that condition gets wrong.  `fd[1]`
      really does hold FMODE_WRITE — `create_pipe_files` opens it
      O_WRONLY — so it passes the second half and fails only the first.
      An `FdPipe` arm that had copied `FdFile`'s "read-only, so no
      FMODE_WRITE" reasoning would therefore have reached the right
      errno on the read end for the wrong reason, and would have had
      nothing to say about the write end.  It is S_ISREG that decides
      here, for both ends, and the model consults the direction bit not
      at all;
    - a writable file fd whose path is absent from `m_fs` is
      `unmodeled`; an `FdFileW` always points into the fs (see openat),
      so this arm is unreachable rather than a judgement;
    - a grow larger than `modeled_truncate_gap` permits is `unmodeled`,
      fail closed, decided after the fd checks Linux makes first.

    WHAT THIS SPEC DOES NOT MODEL, and therefore what it assumes of the
    environment.  Four failures are named below, each from state the
    model does not carry; the list is the set a caller could plausibly
    reach, NOT an exhaustive enumeration of what this path can return.
    `notify_change` (fs/attr.c), which `do_truncate` calls, adds at
    least -EOVERFLOW on an inode whose uid or gid does not map in the
    mount's idmapping, a second LSM veto in `security_inode_setattr`,
    and -EWOULDBLOCK from `try_break_deleg`, which `do_truncate` cannot
    retry because it passes a NULL `delegated_inode`; a filesystem's own
    `i_op->setattr` adds more still (`ext4_setattr` alone has -EIO on a
    shut-down superblock and a THIRD -EFBIG at `s_bitmap_maxbytes`).
    None of those is reachable on a file the run created through the
    modeled openat either, and none changes what this spec ADMITS.

    Each named failure is listed with the DIRECTION that reaches it,
    which is a fact about where the check sits rather than about what it
    means.  Only the two SIZE limits are grow-only, because
    `inode_newsize_ok` (fs/attr.c) consults them solely in its
    `inode->i_size < offset` branch.  -ETXTBSY is the exact COMPLEMENT
    of grow-only rather than direction-independent: it is that
    function's `else` arm, so it needs `i_size >= offset` and a strict
    grow never reaches it.  Only the append-only and LSM pair runs in
    either direction:

    - -EFBIG past RLIMIT_FSIZE, which ALSO raises SIGXFSZ, whose default
      action is to kill the process — GROW-ONLY;
    - -EFBIG past the filesystem's `s_maxbytes` — GROW-ONLY;
    - -EPERM from `IS_APPEND` and -EACCES from an LSM
      (`security_file_truncate`, and `security_path_truncate` before
      v6.6) — EITHER DIRECTION, and the only two of the four decided in
      `do_ftruncate` itself, before `do_truncate` is called;
    - -ETXTBSY when the inode is an active swapfile
      (`inode_newsize_ok`'s `i_size >= offset` branch) — SHRINK OR
      EQUAL, never a grow.

    An immutable inode is -EPERM in either direction too, but it is NOT
    in the entry point: on ext4 it is `ext4_setattr`'s `IS_IMMUTABLE`
    test, reached through `notify_change` -> `i_op->setattr` INSIDE
    `do_truncate`.  `may_setattr`'s own immutable test does not fire
    here, since it is gated on ATTR_MODE/UID/GID/TIMES_SET and
    `do_truncate` sets ATTR_SIZE | ATTR_MTIME | ATTR_CTIME.  Linux v6.1
    through v6.12.

    None is modeled, and no errno is invented for them: the spec commits
    to 0 on a grow it accepts.  The immutable and append-only cases
    cannot arise on a file the run itself created through the modeled
    openat.  The two size limits are assumptions about the environment,
    and the bound does NOT stand in for either: `modeled_truncate_gap`
    bounds the per-call DELTA, while `s_maxbytes` and RLIMIT_FSIZE bound
    the ABSOLUTE size, so they are not comparable quantities and no
    number of in-bound calls is inductively safe.

    RLIMIT_FSIZE is a PREMISE ON THE ENVIRONMENT.  `inode_newsize_ok`
    consults `rlimit(RLIMIT_FSIZE)`, the soft limit, and skips its
    -EFBIG-plus-SIGXFSZ arm on exactly RLIM_INFINITY (fs/attr.c, Linux
    v6.18.46, commit 1f99e9ab748f); this spec's 0 on a grow is right
    under that value and only that value, so the run must start with
    the soft limit at RLIM_INFINITY.  It then stays there: the only writer that can LOWER it during the
    run is `do_prlimit` (kernel/sys.c) — reached through prlimit64,
    whose `Kernel.Sys.prlimit64_spec` declines every resource but
    RLIMIT_CORE, or through setrlimit (164), which has no arm — so a
    program that lowers the limit fails closed at that call and its later
    ftruncate is never judged against this 0.  The one other writer,
    `do_acct_process` (kernel/acct.c), raises the soft limit to
    RLIM_INFINITY around an accounting record and restores it, so it
    cannot make an unlimited process limited.  The
    model carries no rlimit, and that is on purpose: an injectable
    -EFBIG here would be wrong twice — it would admit -EFBIG on shrinks,
    where no kernel produces it, and it would drop the SIGXFSZ that makes
    the process die rather than see the errno.

    `s_maxbytes` is the half nothing checks.  Accumulation reaches it —
    32768 grows of exactly `Uaccess.rw_bytes_max` pass every guard here and
    put the file past vfat's 4 GiB `s_maxbytes`, where the kernel answers
    -EFBIG and this spec says 0.  It is remote rather than closed when
    the cwd is tmpfs, whose `s_maxbytes` is MAX_LFS_FILESIZE =
    LLONG_MAX on a 64-bit kernel (mm/shmem.c shmem_fill_super,
    include/linux/fs.h), and no ftruncate length exceeds that.  It is the
    same shape `ReadWrite.write_spec` has — though the write
    side is the more forgiving of the two: `generic_write_check_limits`
    answers -EFBIG only when the START position is already at or past
    the limit, and CLAMPS a write that merely crosses it into a short
    write.  The model's regular-file write returns the full count
    (`ReadWrite.write_spec`'s `FdFileW` arm is deterministic), so the
    clamp is rejected there exactly as the -EFBIG is; both halves are
    shared.

    -EROFS is deliberately absent, and that is a source-grounded
    difference from truncate(2)'s documented error list: there is no
    `mnt_want_write` and no `inode_permission` on the ftruncate path at
    all. Write access was settled at open time, so a read-only mount
    gives -EROFS at the openat and an -EINVAL here on the O_RDONLY fd
    that results.

    NO -EFBIG CONSTANT IS AVAILABLE, which is why `modeled_truncate_gap`
    is the only thing standing at the top of the range.  `s_maxbytes` is
    a per-filesystem value, and the disagreement is not theoretical:
    measured under qemu-riscv64, `ftruncate(fd, 2^63-1)` answers 0 on
    tmpfs and on overlayfs, and -EFBIG on a virtiofs mount.  So the same
    call is a conforming success in one environment and a conforming
    -EFBIG in another, and a spec that picked either would be wrong in
    the other.  Declining above the bound is the only answer that is
    right in both — and it is a decline, not an errno, because the
    answer is the environment's to give.

    The kernel's fourth check, `small && length > MAX_NON_LFS` ->
    -EINVAL, is unreachable here rather than unmodeled.
    `SYSCALL_DEFINE2(ftruncate, ...)` passes `small = 1` down through
    `do_sys_ftruncate` (fs/open.c), but the O_LARGEFILE clear drops it —
    and every open on a 64-bit kernel sets that flag.  The clear moved
    with the v6.9 split noted above: it is in `do_sys_ftruncate` itself
    through v6.8, and in `do_ftruncate` from v6.9 on.  The flag is forced
    in the syscall entry points themselves, `SYSCALL_DEFINE4(openat, ...)`
    and its siblings in fs/open.c (NOT in `build_open_flags`, which never
    mentions it), from
    `force_o_largefile()`, a macro in include/linux/fcntl.h defined as
    `!IS_ENABLED(CONFIG_ARCH_32BIT_OFF_T)`; and ARCH_32BIT_OFF_T is
    declared in arch/Kconfig with `depends on !64BIT`.  Linux v6.1
    through v6.12.  Measured: `ftruncate(fd, 2^31)` answers 0.

    The success arm is DETERMINISTIC on purpose — no `alt`, no
    `Syscall.errno_from`.  Every failure a real kernel can raise on a grow this
    small comes from state the model does not carry, and inventing an
    injectable set for it would let a source and a target that really
    behave differently share a trace set.  The narrowing is the same one
    `ReadWrite.write_spec` takes for short writes: fewer admitted outcomes, none
    of them unsound. -/
def ftruncate_spec (fd len : word) : SysSpec SyscallEffect :=
  if decide (len.toInt < 0) then err_ret EINVAL
    -- negative length: real -EINVAL, and decided BEFORE the fd lookup
  else
  bind getModelSpec fun m =>
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF                        -- fd not open: real -EBADF
  | some (FdEntry.FdChannel _) => err_ret EINVAL -- no channel is a writable regular file: real -EINVAL, not -ESPIPE
  | some (FdEntry.FdSocket _) => err_ret EINVAL  -- on an fd the model KNOWS is a socket: a socket
                                                 -- inode is S_ISSOCK, so `do_ftruncate`'s
                                                 -- !S_ISREG test answers -EINVAL before FMODE_WRITE
                                                 -- is consulted
  | some (FdEntry.FdPipe _ _) => err_ret EINVAL  -- the same answer for the same reason, on an fd
                                                 -- the model KNOWS is a pipe — see the header
  | some (FdEntry.FdDevNull _ _) => err_ret EINVAL -- and on /dev/null: a character device is not
                                                 -- S_ISREG, so `do_ftruncate` (fs/open.c, v6.18.46)
                                                 -- answers -EINVAL whatever the access mode
  | some FdEntry.FdUrandom => err_ret EINVAL     -- /dev/urandom is a character device too, and
                                                 -- read-only besides: `do_ftruncate`'s `!S_ISREG`
                                                 -- is the same -EINVAL, tested before FMODE_WRITE
  | some (FdEntry.FdFile _ _) => err_ret EINVAL  -- fd open read-only: no FMODE_WRITE, real -EINVAL
  | some FdEntry.FdDir => err_ret EINVAL         -- a directory is not S_ISREG: real -EINVAL, not -EISDIR
  | some (FdEntry.FdFileA p _) =>
      -- AN APPEND FD IS A WRITABLE REGULAR FILE, so it takes the arm
      -- below rather than the -EINVAL the five kinds above get:
      -- `do_ftruncate`'s condition is
      -- `!S_ISREG(inode->i_mode) || !(file->f_mode & FMODE_WRITE)`
      -- (fs/open.c), and an `FdFileA` fails neither half — O_APPEND
      -- rides on O_WRONLY, which is what sets FMODE_WRITE.  The flag is
      -- read nowhere on this path: `do_truncate` sets the size
      -- outright, and O_APPEND is consulted only by the write path's
      -- `generic_write_checks`.  The inode's APPEND-ONLY attribute is a
      -- different thing and does bite here — `IS_APPEND(inode)` is
      -- `do_ftruncate`'s own -EPERM — but it is an inode attribute this
      -- model does not carry, exactly as for `FdFileW`, and the header's
      -- list of unmodeled failures already names it.
      --
      -- THE OFFSET IS UNTOUCHED as it is for every other kind, so a
      -- shrink can leave `f_pos` past end-of-file — this arm writes no
      -- `set_fds` at all, exactly as the `FdFileW` one does not.  On an
      -- append fd that is not observable through a later WRITE, which
      -- repositions itself, but it IS observable through
      -- `lseek(fd, 0, SEEK_CUR)`, so leaving the entry alone is a
      -- decision here rather than a spare line.
      match Fs.fs_lookup (m_fs m) p with
      | none => unmodeled                        -- an FdFileA always points into the fs; see openat
      | some data =>
          if !(modeled_truncate_gap data len) then unmodeled
          else
            seqSpec (set_fs (Fs.fs_set (m_fs m) p (Fs.file_truncate data len)))
              (ret_only (BitVec.ofInt 64 0))
  | some (FdEntry.FdFileW p _) => ftruncate_file_arm p len m
  | some (FdEntry.FdFileRW p _) => ftruncate_file_arm p len m

/- faccessat's injectable failures on the arm that can succeed:
    environment conditions the model does not track, both of them
    reachable on an F_OK probe of a path that really exists.

    - ENOMEM, from the allocations `getname_flags` makes before and
      while it copies: `__getname`, and the `kzalloc` on the re-copy
      path a near-PATH_MAX name takes (fs/namei.c).
      `access_override_creds`'s `prepare_creds` is a third source, but
      it runs only when `access_need_override_creds` says so, and that
      is false for a caller whose fsuid equals its uid and fsgid its
      gid and whose capability set is the uninteresting one for its
      uid — clear for a non-root caller, or identical to the permitted
      set for a root one, both under `!issecure(SECURE_NO_SETUID_FIXUP)`
      (fs/open.c).
    - EACCES, from the path walk's own search-permission check, and from
      that alone.  `may_lookup` takes `inode_permission(..., MAY_EXEC)`
      on the directory the walk starts from — the working directory here
      — in the FIRST iteration of `link_path_walk`, before the last
      component is even typed (fs/namei.c).  So it precedes every answer
      below, the "." and ".." ones included.
      NOT from an LSM: `security_inode_permission` is handed the mask
      with MAY_ACCESS set, and MAY_ACCESS is the bit filesystems branch
      on rather than the bit LSMs do.  The two in-tree hooks that could
      deny both refuse the mask before they compute anything, in the
      same shape and for the same stated reason: `selinux_inode_permission`
      opens with `mask &= MAY_READ|MAY_WRITE|MAY_EXEC|MAY_APPEND` and
      then `if (!mask) return 0;` under the comment "No permission to
      check.  Existence test." (security/selinux/hooks.c), and
      `smack_inode_permission` masks to the same four bits and returns 0
      outright when nothing is left (security/smack/smack_lsm.c).  So
      neither reaches its access-vector computation at all.

    ENOENT is NOT injectable: path existence IS tracked, and an absent
    name is a deterministic -ENOENT.

    WHAT A ZERO MASK EXCLUDES BY ITSELF (Linux fs/open.c,
    `do_faccessat`, byte-identical v6.15 through v6.18.46 — the pinned
    tree — and unchanged in every decision it makes back to v6.6).  Each
    of these is gated on a bit F_OK does not set, so no environment
    reaches it:

    - EROFS.  The read-only test at the end of `do_faccessat` runs only
      when `mode & S_IWOTH`, and `sb_permission`'s own EROFS only when
      `mask & MAY_WRITE`.  A zero mode sets neither, so F_OK returns 0
      on a read-only filesystem.
    - EPERM (immutable) and the unmapped-id EACCES: both inside
      `inode_permission`'s `if (unlikely(mask & MAY_WRITE))`.
    - EACCES from `path_noexec`: gated on `mode & MAY_EXEC` and
      `S_ISREG`.
    - the DAC comparison itself, in every form.  Both of
      `acl_permission_check`'s tests narrow to the low three bits first
      — the fast path is `!((mask & 7) * 0111 & ~mode)` and the owner
      arm is `mask &= 7` then `(mask & ~mode) ? -EACCES : 0` — so a zero
      mask satisfies each outright; and `posix_acl_permission` opens
      with `want &= MAY_READ | MAY_WRITE | MAY_EXEC` and then finds
      every `(e_perm & 0) == 0` (fs/namei.c, fs/posix_acl.c).

    WHAT IS EXCLUDED BY THE ENVIRONMENT INSTEAD, and so is a precondition
    rather than a gate.  These reach a zero mask and can answer outside
    `faccessat_errnos`; the WORLD paragraph on `faccessat_spec` is what
    rules them out, and a run that leaves it is a false rejection rather
    than an unsound admission:

    - `do_inode_permission` dispatches to `inode->i_op->permission`
      ahead of `generic_permission` and passes the mask through
      unfiltered (fs/namei.c).  MAY_ACCESS is exactly the bit some
      filesystems read: `fuse_permission` turns it into a FUSE_ACCESS
      request whose errno the userspace server picks (fs/fuse/dir.c),
      and `proc_pid_permission` can answer -ESRCH or, under hidepid,
      -ENOENT or -EPERM with a zero mask (fs/proc/base.c).
    - `devcgroup_inode_permission` returns early only for a non-device
      inode; on a block or character node under a restrictive device
      cgroup it reaches `__devcgroup_check_permission` and can answer
      -EPERM even with an empty access set
      (include/linux/device_cgroup.h, security/device_cgroup.c).
    - `posix_acl_permission` and `check_acl` can answer -EIO on a
      malformed or unreadable on-disk ACL (fs/posix_acl.c).
    - -ESTALE, after `do_faccessat`'s own `retry_estale` loop has
      re-resolved once with LOOKUP_REVAL and failed again.

    ETXTBSY is not in either list because `do_faccessat` has no path to
    it at all: nothing in its body calls `get_write_access` or tests
    `IS_SWAPFILE`. -/

def faccessat_errnos : List Int := [ENOMEM, EACCES]

/-- `mode` as `do_faccessat` reads it: the low 32 bits of the register,
    since the parameter is declared `int` (`Syscall.int32`). -/
def access_mode (mode : word) : Int := ((int32 mode).toNat : Int)

/-- The mode words the kernel accepts at all: `mode & ~S_IRWXO` zero.
    Like `Fs.Namei.modeled_unlink_flags` this is not a modeling choice —
    a word outside it is the kernel's own -EINVAL, not `unmodeled`.
    Note that a NEGATIVE `mode` lands here: `access(p, -1)` truncates to
    0xffffffff, whose bits outside the mask are set, so it is -EINVAL. -/
def modeled_access_mode (mode : word) : Bool :=
  z_ldiff (access_mode mode) S_IRWXO == 0

/-- F_OK — the empty mode, and the only one this model can answer. -/
def access_mode_f_ok (mode : word) : Bool := access_mode mode == 0

/-- The one outcome an F_OK probe of a path that RESOLVES admits: 0, or
    one of the untracked environment failures above.  Both take a bare
    return and every one of the five ledgers empty — faccessat writes
    nothing, zeroes nothing, unmaps nothing and copies out nothing, and
    the pathname copy-in is the wrapper's — and neither touches
    the model, which is what makes this syscall a pure observation. -/
def access_exists_spec : SysSpec SyscallEffect :=
  alt (bind (errno_from faccessat_errnos) (fun e => err_ret e))  -- untracked env failure
      (ret_only (BitVec.ofInt 64 0))

/-- `faccessat dirfd path mode` (riscv64 nr 48, `SYSCALL_DEFINE3`),
    which is `do_faccessat(dfd, filename, mode, 0)` — the flags word is
    a CONSTANT ZERO here, not an argument.  AT_EACCESS,
    AT_SYMLINK_NOFOLLOW and AT_EMPTY_PATH are reachable only through
    `faccessat2` (nr 439, `SYSCALL_DEFINE4`), which `faccessat2_spec`
    below answers, so nothing in THIS spec interprets a flag: there is
    no flag to interpret.  That also fixes the empty pathname at
    -ENOENT, since AT_EMPTY_PATH is the only thing that would make
    `getname_flags` accept it, and no `faccessat` can pass it.

    ONLY F_OK IS MODELED, and the reason is the model's file system.
    `Fs` maps a path to its BYTES and holds nothing else — no mode bits,
    no owner, no mount.  R_OK, W_OK and X_OK are answered by
    `generic_permission` out of `inode->i_mode` against the caller's
    ids (fs/namei.c, `acl_permission_check`), and W_OK reaches
    `__mnt_is_readonly` besides.  None of that is a function of the byte
    map, so a mode with any of the low three bits set is `unmodeled`.
    F_OK asks the one question the map can answer: does this path
    resolve.

    THE REAL-UID RULE IS WHAT MAKES THAT SLICE SOUND rather than merely
    convenient.  `access(2)` exists to check with the REAL ids, and
    `do_faccessat` implements that by installing an override cred whose
    fsuid/fsgid are copied from uid/gid (`access_override_creds`) — the
    historically delicate part of this syscall, and the part the model
    does not track, since `State` carries uid and euid but no fsuid.
    Under F_OK it is unobservable.  The mask handed to
    `inode_permission` is `0 | MAY_ACCESS`, and MAY_ACCESS is outside
    the MAY_READ|MAY_WRITE|MAY_EXEC triple every DAC comparison narrows
    to: `acl_permission_check`'s test is `(mask & 7) * 0111 & ~mode`,
    which is 0 for a zero mask, and `posix_acl_permission` opens with
    `want &= MAY_READ | MAY_WRITE | MAY_EXEC` and then finds every
    `(e_perm & 0) == 0` (fs/namei.c, fs/posix_acl.c).  So which cred is
    installed changes no answer F_OK gives, and the only trace the
    override leaves is the -ENOMEM already in `faccessat_errnos`.
    THIS STOPS BEING TRUE the moment a nonzero mode is modeled: at that
    point fsuid is load-bearing and has to be carried in `State` first.

    ORDER, following the kernel's exactly (fs/open.c, `do_faccessat`):

    - the mode word first, and it really is first — `if (mode & ~S_IRWXO)
      return -EINVAL;` is the opening statement of the function, ahead of
      the flag test, ahead of `access_need_override_creds` and ahead of
      `user_path_at`.  So `faccessat(AT_FDCWD, NULL, 8)` is -EINVAL and
      not -EFAULT: the user pointer is never dereferenced.  The spec
      records no pathname copy-in on that arm for the same reason.
    - then, for a mode this model declines, `unmodeled` — before the
      pathname, so the spec makes no claim about an -EFAULT it could not
      then judge anyway.
    - then `getname()` inside `user_path_at`, with all three of its
      answers as `openat_spec` has them: -ENAMETOOLONG for no NUL within
      PATH_MAX, -ENOENT for the empty string, -EFAULT for an unmapped
      byte.
    - only then the dirfd, resolved in `path_init`: the relative-to-a-
      dirfd modes are not modeled, so any dirfd but AT_FDCWD is
      `unmodeled`, the same treatment `openat_spec` and
      `Fs.Namei.unlinkat_spec` give it.

    THE ANSWERS, once the path is in hand.  "." and ".." resolve without
    consulting the byte map: "." is the working directory and ".." its
    parent, and both exist by construction, so both are the existence
    arm.  (`link_path_walk` types them LAST_DOT and LAST_DOTDOT and
    `handle_dots` answers them; neither reaches a filesystem lookup, and
    an UNLINKED working directory is still 0 — `complete_walk` has no
    `d_unlinked` test on this path.)  Every flag-gated failure the ".."
    walk can raise is unreachable here, because `do_faccessat` builds
    `lookup_flags` from a zero flag word and never sets one of them:
    `handle_dots`'s -EAGAIN under LOOKUP_IS_SCOPED, and both of
    `follow_dotdot`'s -EXDEVs, the LOOKUP_NO_XDEV one and the
    LOOKUP_BENEATH one on its `in_root` branch.  The failure that is NOT
    flag-gated is `path_connected`'s -ENOENT, raised when the working
    directory has been renamed out from under a bind-mount root; it is
    reachable and is not admitted here, and sits under the same world
    precondition as everything else below (fs/namei.c).  For an ordinary name the map is the answer: a
    key present is the existence arm, a key absent is -ENOENT.

    THE WORLD this is exact in is the one `openat_spec` and
    `Fs.Namei.unlinkat_spec` already depend on: every model key is a
    regular file directly in the working directory, and the working
    directory holds nothing but those keys.  The three guards
    `Fs.Namei.unlinkat_spec` uses to stay inside it are needed here for
    the same reasons, and one of them for a DIFFERENT reason worth
    stating:

    - a path containing "/" is `unmodeled`.  The kernel resolves every
      component; the flat map's confident answer for "a/b" is "absent,
      -ENOENT" and reality may hold a directory "a" with a file "b" in
      it.  This is the same bound the slash guard puts on `unlinkat`,
      and it bounds this spec exactly as hard: no absolute path, no
      trailing slash, no multi-component name.
    - a single component longer than `Uapi.NAME_MAX` is `unmodeled`:
      `getname()`'s PATH_MAX bound lets a 4095-byte component through
      and the FILESYSTEM then answers -ENAMETOOLONG, which the model has
      no filesystem type to ask.
    - a name some key lives UNDER (`Fs.Namei.fs_under`) is `unmodeled`.
      For `unlinkat` that guard prevents a wrong ERRNO; here it prevents
      a wrong SUCCESS-OR-NOT.  A key "a/b" means reality has a directory
      "a", and F_OK of a directory returns 0 where the map would answer
      -ENOENT.

    WHAT NO GUARD RESTORES is the second half of that world: a real
    directory entry the map does not hold.  An EMPTY real directory has
    no key under it, so `fs_under` sees nothing, `fs_lookup` misses, and
    this spec answers -ENOENT where Linux answers 0.  The same holds for
    a symlink, a fifo, a socket or a device node in the working
    directory.  That is a false REJECTION rather than an unsound
    admission — the checker refuses a trace Linux really produced — and
    it is the flat-namespace gap `newfstatat` and `openat` already
    have.  It costs the most here, where an existence probe of a
    directory is a shape real programs reach for.  No modeled syscall
    creates a directory, so it is an environment precondition rather
    than something a guard could close.

    APPROXIMATION, the same one `openat_spec` carries, on every
    deterministic arm: they admit that ONE answer and no
    `faccessat_errnos` alternative, so they exclude the -ENOMEM
    `getname_flags` and `access_override_creds` can raise first, and the
    -ENOENT of an absent name additionally preempts the -EACCES a
    search-permission failure on the working directory would raise
    during resolution.  That narrows the spec rather than widening it,
    so it admits nothing unsound; the cost is that a source and a target
    diverging only under allocation failure are not distinguished by the
    proved theorem. -/
def faccessat_body_spec (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : SysSpec SyscallEffect :=
  match read_cstr (i.in_mem) pathp with
  | .CstrTooLong => err_ret ENAMETOOLONG          -- no NUL within PATH_MAX
  | .CstrFault => err_ret EFAULT                  -- unmapped byte in the path string
  | .CstrOk p =>
      if Fs.path_eqb p [] then err_ret ENOENT     -- empty pathname: getname's own -ENOENT
      else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
      else if Fs.path_eqb p dot_path then access_exists_spec      -- the working directory
      else if Fs.path_eqb p dotdot_path then access_exists_spec   -- its parent
      else if path_has_slash p then unmodeled    -- no directory structure: see WORLD above
      else if decide (NAME_MAX < p.length) then unmodeled  -- the filesystem's own -ENAMETOOLONG
      else if fs_under (m_fs m) p then unmodeled -- p names an implied directory
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => err_ret ENOENT                   -- absent: real -ENOENT, not a modeling gap
      | some _ => access_exists_spec

/-- The mode word, then the body under its copy-in ledger.

    THE PATHNAME COPY-IN is recorded exactly as `openat_spec` records
    it, and for the same reason: `read_cstr` is a read of user memory,
    and `State.syscall_effect_accesses` turns the ledger into a
    materialization charge, so an unrecorded read is a page the run
    never pays for.  Both mode arms sit OUTSIDE the wrapper, as
    `Fs.Namei.unlinkat_spec`'s flag arm does: the -EINVAL is a real
    answer the kernel reaches before `user_path_at` is called, so
    recording a copy there would claim a read Linux did not perform, and
    the `unmodeled` arm claims nothing at all. -/
def faccessat_spec (dirfd pathp mode : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
  if !(modeled_access_mode mode) then err_ret EINVAL
  else if !(access_mode_f_ok mode) then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux (i.in_mem) pathp path_max)]
      (faccessat_body_spec dirfd pathp i m)

/-- `flags` as `do_faccessat` reads it: the low 32 bits of the register,
    since `SYSCALL_DEFINE4(faccessat2, ...)` declares the parameter
    `int` (`Syscall.int32`), exactly as `access_mode` reads the mode. -/
def access_flags (flags : word) : Int := ((int32 flags).toNat : Int)

/-- The three flags `do_faccessat` accepts at all
    (include/uapi/linux/fcntl.h; the test is
    `if (flags & ~(AT_EACCESS | AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH))
     return -EINVAL;`, fs/open.c). -/
def access_flags_mask : Int :=
  z_lor AT_EACCESS (z_lor AT_SYMLINK_NOFOLLOW AT_EMPTY_PATH)

/-- The flag words the kernel accepts at all.  Like
    `modeled_access_mode` this is not a modeling choice: a word outside
    it is the kernel's own -EINVAL, not `unmodeled`.  A NEGATIVE flags
    argument lands here too, for the reason `modeled_access_mode` gives
    for a negative mode: it truncates to 0xffffffff, whose bits outside
    the mask are set. -/
def valid_access_flags (flags : word) : Bool :=
  z_ldiff (access_flags flags) access_flags_mask == 0

/-- The accepted flag words this model ANSWERS: the two that change no
    answer it can give.  AT_EMPTY_PATH is the one it declines, and the
    decline is a decline rather than an -EINVAL because the kernel
    accepts the bit.  See `faccessat2_spec` for both arguments. -/
def modeled_access_flags (flags : word) : Bool :=
  z_land (access_flags flags) AT_EMPTY_PATH == 0

/-- `faccessat2 dirfd path mode flags` (riscv64 nr 439,
    `SYSCALL_DEFINE4`), which is `do_faccessat(dfd, filename, mode,
    flags)` — the same function `faccessat` reaches with a constant zero
    flag word (fs/open.c, v6.18.46).  So everything `faccessat_spec`
    says about the mode, the pathname, the dirfd and the answers holds
    here unchanged, and this spec adds exactly one thing: what the flag
    word does.

    ORDER, following the kernel's exactly (fs/open.c, `do_faccessat`).
    The two -EINVAL tests are the function's first two statements, in
    this order, both ahead of `access_need_override_creds` and ahead of
    `user_path_at`:

    - `if (mode & ~S_IRWXO) return -EINVAL;`
    - `if (flags & ~(AT_EACCESS | AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH))
       return -EINVAL;`

    THE SECOND ONE IS WHY THIS SPEC DOES NOT DECLINE ON THE MODE FIRST.
    A call with, say, `mode = R_OK` and a garbage flag word is a
    deterministic -EINVAL that Linux decides without ever consulting the
    permission machinery this model lacks; declining it would refuse a
    trace Linux really produces, and answering -EINVAL from the mode
    would name the wrong test.  So both -EINVAL arms come first, in the
    kernel's own order, and only then do the two declines.  Both -EINVAL
    arms sit OUTSIDE the copy-in wrapper, as `faccessat_spec`'s does:
    the pathname is never fetched on either.

    WHAT EACH ACCEPTED FLAG DOES, and why F_OK cannot see it.

    - AT_EACCESS is read once, by `access_need_override_creds`, which
      returns false outright when it is set (fs/open.c).  The effect is
      that `access_override_creds` is not called and the walk runs with
      the caller's fsuid/fsgid rather than with uid/gid copied over
      them.  `faccessat_spec`'s REAL-UID paragraph already argues that
      which of the two creds is installed changes no answer F_OK gives:
      the mask handed to `inode_permission` is `0 | MAY_ACCESS`, and
      MAY_ACCESS is outside the MAY_READ|MAY_WRITE|MAY_EXEC triple every
      DAC comparison narrows to (`acl_permission_check` and
      `posix_acl_permission`, fs/namei.c and fs/posix_acl.c).  That
      argument is symmetric in the two creds, so it covers AT_EACCESS
      set exactly as it covers AT_EACCESS clear.  The one asymmetry is
      an errno the model already admits from elsewhere: with AT_EACCESS
      set, `prepare_creds` never runs, so its -ENOMEM cannot arise —
      but `__getname`'s can, and that is the -ENOMEM
      `faccessat_errnos` is there for.  Admitting the same set on both
      arms is therefore sound; it is not tighter than it could be
      because the tighter set is the same set.

    - AT_SYMLINK_NOFOLLOW clears LOOKUP_FOLLOW, so a TRAILING SYMLINK is
      not followed and the link itself is what F_OK asks about
      (fs/open.c builds `lookup_flags` from it; fs/namei.c walks with
      it).  Under the WORLD `faccessat_spec` states — every model key a
      regular file directly in the working directory, and the working
      directory holding nothing but those keys — there is no symlink for
      the bit to change, at the last component or at any other: a
      resolvable name is a regular file, which resolves identically with
      the bit set and clear, and "." and ".." are typed LAST_DOT and
      LAST_DOTDOT and answered by `handle_dots` without a link ever
      being read.  A multi-component path, where an INTERMEDIATE symlink
      would be followed whatever this bit says, is declined by the slash
      guard before the bit is reached; a trailing slash, which
      `lookup_last` answers by putting LOOKUP_FOLLOW back
      (`nd->last.name[nd->last.len]` nonzero, fs/namei.c), is declined
      by the same guard.  So this flag is admitted under the SAME
      precondition the rest of the spec already needs, and it widens
      nothing: leaving the world costs a false rejection here exactly as
      it does there.

    - AT_EMPTY_PATH is DECLINED, and the decline is the honest one
      rather than an -EINVAL: the kernel accepts the bit, turning it
      into LOOKUP_EMPTY so that `getname_flags` admits the empty string
      and the dirfd itself becomes the target (fs/namei.c).  That makes
      the empty pathname resolve to the working directory instead of
      answering -ENOENT — the opposite of the arm `faccessat_body_spec`
      carries — so the bit is not one this spec can pass through, and
      the model declines it BEFORE the pathname is read.  The decline is
      unconditional in the flag rather than conditioned on the pathname
      being empty, which costs the (equally answerable) case of
      AT_EMPTY_PATH beside a nonempty name and buys a bound a reader can
      check without re-deriving where LOOKUP_EMPTY is consulted.

    EVERY OTHER FLAG the kernel would accept is a bit outside the three,
    and the kernel's own -EINVAL. -/
def faccessat2_spec (dirfd pathp mode flags : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
  if !(modeled_access_mode mode) then err_ret EINVAL
  else if !(valid_access_flags flags) then err_ret EINVAL
  else if !(modeled_access_flags flags) then unmodeled
  else if !(access_mode_f_ok mode) then unmodeled
  else
    record_copyins [(pathp, cstr_access_len_aux (i.in_mem) pathp path_max)]
      (faccessat_body_spec dirfd pathp i m)


/- =========================================================================
   Port checks

   These are PORT CHECKS, not reused lemmas.  They pin the two
   things a transcription slip would break: the decidable flag/mode
   arithmetic, and the outcome each arm actually reaches on a concrete
   model.  The `by decide` ones run the definition; the outcome ones go
   through the helper theorems below, which are PORT SCAFFOLDS (the
   shape a caller reaches, stated once so the check reads as the fact it
   pins).
   ========================================================================= -/

/-- The empty model the outcome checks run on: no descriptors, an empty
    file system, silent stdin.  `mkModel` is `StateLedger`'s. -/
def chk_model : Model := mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- A syscall input whose memory is the byte list `bs` starting at
    address 0 — enough for `read_cstr` to see a NUL-terminated pathname. -/
def chk_input (bs : List byte) : SyscallInput :=
  { in_sysno := 0, in_args := [], in_mem := fun a => (bs.drop a.toNat).head?,
    in_wmem := fun _ => none }

/-- A model holding one write-only descriptor (`fd`) on one file. -/
def chk_model_file (fd : word) (p : Fs.path) (data : List byte) : Model :=
  mkModel [(fd, FdEntry.FdFileW p (BitVec.ofInt 64 0))] (mkVmMaps [] [] 0 0 0) IEof
    [(p, data)]

/-! ### The decidable helpers -/

-- the admitted flag words, and one that is not
example : modeled_open_flags (BitVec.ofInt 64 0) = true := by decide
example : modeled_open_flags (BitVec.ofInt 64 wr_create_flags) = true := by decide
example : modeled_open_flags (BitVec.ofInt 64 (O_RDWR + O_CREAT)) = true := by decide
example : modeled_open_flags (BitVec.ofInt 64 0x400000) = false := by decide  -- O_TMPFILE
-- the exclusive words, with and without the inert O_TRUNC
example : is_excl_create excl_create_flags = true := by decide
example : is_excl_create (excl_create_flags + O_TRUNC) = true := by decide
example : is_excl_create wr_create_flags = false := by decide
example : is_rdwr_excl_create rdwr_excl_create_flags = true := by decide
example : rdwr_open_word (O_RDWR + O_TRUNC) = true := by decide
example : flag_set (O_RDWR + O_CREAT) O_CREAT = true := by decide
example : flag_set O_RDWR O_CREAT = false := by decide

-- path shapes
example : path_is_dirref dot_path = true := by decide
example : path_is_dirref dotdot_path = true := by decide
example : path_is_dirref [0x61] = false := by decide
example : path_has_slash dot_path = false := by decide
example : path_has_slash [0x61, 0x2f, 0x62] = true := by decide
example : openat_plain_name [0x61] = true := by decide
example : openat_plain_name dot_path = false := by decide
example : fs_under [([0x61, 0x2f, 0x62], [])] [0x61] = true := by decide
example : fs_under [([0x61, 0x2f, 0x62], [])] [0x61, 0x2f, 0x62] = false := by decide
example : tmp_name (tmp_prefix ++ [0x61]) = some [0x61] := by decide
example : tmp_name (tmp_prefix ++ [0x61, 0x2f, 0x62]) = none := by decide

-- the truncate gap: a grow inside the band is judged, a huge one is not
example : modeled_truncate_gap [0x61] 3 = true := by decide
example : modeled_truncate_gap [0x61] 0 = true := by decide
example : modeled_truncate_gap [0x61] (BitVec.ofInt 64 (2 ^ 40)) = false := by decide
-- and the file algebra it feeds: shrink drops the tail, grow zero-fills
example : Fs.file_truncate [0x61, 0x62, 0x63] 2 = [0x61, 0x62] := by decide
example : Fs.file_truncate [0x61, 0x62, 0x63] 5 = [0x61, 0x62, 0x63, 0, 0] := by decide
example : Fs.file_truncate [0x61] 1 = [0x61] := by decide

-- faccessat's mode and flag words
example : access_mode (BitVec.ofInt 64 0) = 0 := by decide
example : modeled_access_mode (BitVec.ofInt 64 4) = true := by decide   -- R_OK
example : access_mode_f_ok (BitVec.ofInt 64 4) = false := by decide
example : modeled_access_mode (BitVec.ofInt 64 8) = false := by decide  -- a bit outside S_IRWXO
example : modeled_access_mode (BitVec.ofInt 64 (-1)) = false := by decide
example : valid_access_flags (BitVec.ofInt 64 0) = true := by decide
example : valid_access_flags (BitVec.ofInt 64 8) = false := by decide
example : modeled_access_flags (BitVec.ofInt 64 0) = true := by decide
example : modeled_access_flags (BitVec.ofInt 64 AT_EMPTY_PATH) = false := by decide
example : access_flags_mask = 4864 := by decide

/-! ### Port scaffolds: the success shapes the checks name -/

/-- PORT SCAFFOLD: `create_wronly`'s success arm — the lowest free fd,
    bound to a write-only entry on `p`, with `p` (re)created empty. -/
theorem create_wronly_ok (p : Fs.path) (m : Model) (i : SyscallInput) (fd : word)
    (Hfree : fd_lookup (m_fds m) fd = none) (Halloc : fd = alloc_fd (m_fds m)) :
    create_wronly p m i m
      (.ok (mkEffect fd [] [])
        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
          (with_fs (Fs.fs_set (m_fs m) p []) m)) []) := by
  refine Or.inr ⟨fd, m, [], [], ⟨fd, ⟨Hfree, Halloc⟩, rfl⟩, ?_, rfl⟩
  refine ⟨(), with_fs (Fs.fs_set (m_fs m) p []) m, [], [], rfl, ?_, rfl⟩
  exact ⟨(), _, [], [], rfl, rfl, rfl⟩

/-- PORT SCAFFOLD: `ftruncate`'s writable-regular-file arm — a shrink
    drops the tail, a grow zero-fills, and the fd's offset is untouched
    (no `set_fds`). -/
theorem ftruncate_spec_filew (fd len : word) (i : SyscallInput) (m : Model)
    (p : Fs.path) (off : word) (data : List byte)
    (Hlen : decide (len.toInt < 0) = false)
    (Hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdFileW p off))
    (Hfs : Fs.fs_lookup (m_fs m) p = some data)
    (Hgap : modeled_truncate_gap data len = true) :
    ftruncate_spec fd len i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_truncate data len)) m) []) := by
  unfold ftruncate_spec
  simp only [Hlen]
  refine ⟨m, m, [], [], rfl, ?_, rfl⟩
  dsimp only
  rw [Hfd]
  simp only [ftruncate_file_arm, Hfs, Hgap, Bool.not_true]
  exact ⟨(), _, [], [], rfl, rfl, rfl⟩

/-- PORT SCAFFOLD: `ftruncate` on a read-only file fd — no FMODE_WRITE,
    so -EINVAL (and not the -EBADF of a closed fd). -/
theorem ftruncate_spec_ro (fd len : word) (i : SyscallInput) (m : Model)
    (p : Fs.path) (off : word)
    (Hlen : decide (len.toInt < 0) = false)
    (Hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdFile p off)) :
    ftruncate_spec fd len i m (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  unfold ftruncate_spec
  simp only [Hlen]
  refine ⟨m, m, [], [], rfl, ?_, rfl⟩
  dsimp only
  rw [Hfd]
  rfl

/-! ### The arms -/

/-- PORT CHECK: `openat` of a path the image does not hold is `-ENOENT`
    (O_RDONLY of "a" on the empty model). -/
example :
    openat_body_spec (chk_input [0x61, 0x00]) chk_model AT_FDCWD32 0
      (BitVec.ofInt 64 0) (chk_input [0x61, 0x00]) chk_model
      (.ok (mkEffect (errno_ret ENOENT) [] []) chk_model []) :=
  rfl

/-- PORT CHECK: the WHOLE `openat` spec — flag guard, pathname fetch,
    body and copy-in ledger — on the missing path: `-ENOENT`, with the
    pathname range recorded and the model untouched. -/
example :
    openat_spec AT_FDCWD32 0 (BitVec.ofInt 64 0) (chk_input [0x61, 0x00]) chk_model
      (.ok (with_copyins
              [(0, cstr_access_len_aux (chk_input [0x61, 0x00]).in_mem 0 path_max)]
              (mkEffect (errno_ret ENOENT) [] []))
        chk_model []) := by
  refine ⟨chk_input [0x61, 0x00], chk_model, [], [], rfl, ?_, rfl⟩
  refine ⟨mkEffect (errno_ret ENOENT) [] [], chk_model, [], [], ?_, rfl, rfl⟩
  refine ⟨chk_input [0x61, 0x00], chk_model, [], [], rfl, ?_, rfl⟩
  refine ⟨chk_model, chk_model, [], [], rfl, ?_, rfl⟩
  rfl

/-- PORT CHECK: a creating open (`O_WRONLY|O_CREAT|O_TRUNC` of "a" on
    the empty model) inserts the path, binds the lowest free fd — 0 — to
    a write-only entry on it, and returns that fd. -/
example :
    openat_create_spec [0x61] chk_model (chk_input []) chk_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_fds
          (fd_insert (m_fds chk_model) (BitVec.ofInt 64 0)
            (FdEntry.FdFileW [0x61] (BitVec.ofInt 64 0)))
          (with_fs (Fs.fs_set (m_fs chk_model) [0x61] []) chk_model)) []) :=
  create_wronly_ok [0x61] chk_model (chk_input []) (BitVec.ofInt 64 0) rfl rfl

/-- PORT CHECK: the created file is really in the image the spec returns. -/
example :
    Fs.fs_lookup
      (m_fs (with_fds
        (fd_insert (m_fds chk_model) (BitVec.ofInt 64 0)
          (FdEntry.FdFileW [0x61] (BitVec.ofInt 64 0)))
        (with_fs (Fs.fs_set (m_fs chk_model) [0x61] []) chk_model))) [0x61] = some [] :=
  rfl

/-- PORT CHECK: `close` of an fd the process does not hold is `-EBADF`. -/
example :
    close_spec 3 (chk_input []) chk_model
      (.ok (mkEffect (errno_ret EBADF) [] []) chk_model []) :=
  ⟨chk_model, chk_model, [], [], rfl, rfl, rfl⟩

/-- PORT CHECK: a SHRINK drops the tail and leaves the fd's offset alone
    (no `set_fds` on the arm). -/
example :
    ftruncate_spec 3 2 (chk_input []) (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_fs (Fs.fs_set (m_fs (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])) [0x61]
          (Fs.file_truncate [0x61, 0x62, 0x63] 2))
          (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])) []) :=
  ftruncate_spec_filew 3 2 (chk_input []) (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])
    [0x61] (BitVec.ofInt 64 0) [0x61, 0x62, 0x63] (by decide) rfl rfl (by decide)

/-- PORT CHECK: a GROW zero-fills the region it opens. -/
example :
    ftruncate_spec 3 5 (chk_input []) (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_fs (Fs.fs_set (m_fs (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])) [0x61]
          (Fs.file_truncate [0x61, 0x62, 0x63] 5))
          (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])) []) :=
  ftruncate_spec_filew 3 5 (chk_input []) (chk_model_file 3 [0x61] [0x61, 0x62, 0x63])
    [0x61] (BitVec.ofInt 64 0) [0x61, 0x62, 0x63] (by decide) rfl rfl (by decide)

/-- PORT CHECK: a NEGATIVE length is `-EINVAL`, and it is decided before
    the fd lookup — fd 3 here is live, and the answer is still -EINVAL. -/
example :
    ftruncate_spec 3 (BitVec.ofInt 64 (-1)) (chk_input [])
      (chk_model_file 3 [0x61] [0x61])
      (.ok (mkEffect (errno_ret EINVAL) [] []) (chk_model_file 3 [0x61] [0x61]) []) :=
  rfl

/-- PORT CHECK: `ftruncate` on a read-only file fd is `-EINVAL`, not
    -EBADF and not -EISDIR. -/
example :
    ftruncate_spec 3 1 (chk_input [])
      (mkModel [(3, FdEntry.FdFile [0x61] (BitVec.ofInt 64 0))] (mkVmMaps [] [] 0 0 0)
        IEof [([0x61], [0x61])])
      (.ok (mkEffect (errno_ret EINVAL) [] [])
        (mkModel [(3, FdEntry.FdFile [0x61] (BitVec.ofInt 64 0))] (mkVmMaps [] [] 0 0 0)
          IEof [([0x61], [0x61])]) []) :=
  ftruncate_spec_ro 3 1 (chk_input [])
    (mkModel [(3, FdEntry.FdFile [0x61] (BitVec.ofInt 64 0))] (mkVmMaps [] [] 0 0 0)
      IEof [([0x61], [0x61])]) [0x61] (BitVec.ofInt 64 0) (by decide) rfl

/-- PORT CHECK: `faccessat` F_OK on a path the image does not hold is
    `-ENOENT` (the existence arm is not taken). -/
example :
    faccessat_body_spec AT_FDCWD32 0 (chk_input [0x61, 0x00]) chk_model
      (chk_input [0x61, 0x00]) chk_model
      (.ok (mkEffect (errno_ret ENOENT) [] []) chk_model []) :=
  rfl

/-- PORT CHECK: `faccessat` F_OK on a path the image HOLDS is 0 — the
    existence arm, which changes nothing. -/
example :
    faccessat_body_spec AT_FDCWD32 0 (chk_input [0x61, 0x00])
      (chk_model_file 3 [0x61] [0x41]) (chk_input [0x61, 0x00])
      (chk_model_file 3 [0x61] [0x41])
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) (chk_model_file 3 [0x61] [0x41]) []) :=
  Or.inr rfl

/-- PORT CHECK: a mode this model cannot answer (R_OK) is `unmodeled`,
    before the pathname is even read. -/
example :
    faccessat_spec AT_FDCWD32 0 (BitVec.ofInt 64 4)
      (chk_input [0x61, 0x00]) chk_model .unmodeled := by
  have h1 : (!(modeled_access_mode (BitVec.ofInt 64 4))) = false := by decide
  have h2 : (!(access_mode_f_ok (BitVec.ofInt 64 4))) = true := by decide
  refine bind_unmodeled2 inputSpec _ _ _ _ _ [] rfl ?_
  refine bind_unmodeled2 getModelSpec _ _ _ _ _ [] rfl ?_
  simp only [h1, h2, Bool.false_eq_true, reduceIte, unmodeled]

/-- PORT CHECK: a mode word outside `S_IRWXO` is the kernel's own
    -EINVAL, not `unmodeled`, and it is decided before the pathname. -/
example :
    faccessat_spec AT_FDCWD32 0 (BitVec.ofInt 64 8)
      (chk_input [0x61, 0x00]) chk_model
      (.ok (mkEffect (errno_ret EINVAL) [] []) chk_model []) := by
  have h : (!(modeled_access_mode (BitVec.ofInt 64 8))) = true := by decide
  refine ⟨chk_input [0x61, 0x00], chk_model, [], [], rfl, ?_, rfl⟩
  refine ⟨chk_model, chk_model, [], [], rfl, ?_, rfl⟩
  simp only [h, reduceIte, err_ret, ret_only, pure]

/-- PORT CHECK: an unsupported flag word is `unmodeled`, and the decline
    happens BEFORE the pathname is fetched.  Stated for every flag word
    `modeled_open_flags` refuses, so it is the property, not an instance. -/
theorem openat_core_spec_unmodeled (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) (H : modeled_open_flags flags = false) :
    openat_core_spec dirfd pathp flags i m .unmodeled := by
  unfold openat_core_spec
  refine bind_unmodeled2 inputSpec _ _ _ _ _ [] rfl ?_
  refine bind_unmodeled2 getModelSpec _ _ _ _ _ [] rfl ?_
  simp [H, unmodeled]

/-- PORT CHECK: `O_TMPFILE` — a flag the model does not interpret — is
    declined, on any pathname. -/
example (i : SyscallInput) (m : Model) (pathp : word) :
    openat_core_spec AT_FDCWD32 pathp (BitVec.ofInt 64 0x400000) i m .unmodeled :=
  openat_core_spec_unmodeled _ _ _ _ _ (by decide)

