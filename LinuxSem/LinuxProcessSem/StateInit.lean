/-
  * LinuxProcessSem.StateInit — the run's input, its private /tmp, the initial model

  - 4910–4967: the run's private `/tmp` as keys of the flat file system
    (`tmp_prefix` 4930, `tmp_key` 4934, `tmp_nul_free` 4943,
    `fs_seed_tmp` 4961);
  - 4968–5048: the five seeding lemmas (`fs_seed_tmp_nil` 4968,
    `tmp_prefix_nul_free` 4971, `tmp_key_nul_free` 4978,
    `fs_seed_tmp_valid` 4998, `fs_seed_tmp_keys` 5016) and the one that
    reads an absolute key back (`seeded_absolute_key_is_tmp` 5042);
  - 5150–5299: `ProcInput`, the fifteen-field record of what the caller
    supplies to a run, with the per-field rationale;
  - 5264–5311: `mkProcInput`, the thirteen-place positional form;
  - 5313–5330: `in_fs`, the image with the declared `/tmp` seeded in;
  - 5332–5400: `init_model` (5370) and `init_model_noaccess_nonzero`
    (5396), under the section header that says what each argument is.

  `vm_noaccess_entries_nonzero` (4901) and
  `noaccess_pages_owned_nonzero` (4906) sit just BEFORE this range and are
  already ported in `StateVm.lean` (chunk B7); `init_model_noaccess_nonzero`
  uses them from there, so they are not repeated here.

  trailing block at 5402–5416 (the `(** * The setter/accessor
  interactions, as REWRITES rather than reductions. ... *)` note) is carried
  at the end of this file as a section comment: it introduces the rewrite
  matrix that chunk **B9** owns, and it is not a declaration.

  TRUST BOUNDARY: this file is part of the trusted specification.


  - `init_model`'s body is `with_*` tower in the same order;
    Lean's `{ m with … }` setters are definitional, so the record shape is
    identical and `m_fs (init_model _ _ _ _ _ inp) = in_fs inp` still holds
    by `rfl`.
-/
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.StateStreams

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/- =========================================================================
   The run's private /tmp, as keys of the flat file system
   ========================================================================= -/

/-- "/tmp/" — the prefix under which the run's declared PRIVATE
    temporary directory is carried in the flat map (`Fs.Fs`).

    WHY THE KEY IS ABSOLUTE.  The model has no directory structure and
    no working directory, so "the file `out.gif` inside /tmp" has to be
    a key like any other.  Spelling it exactly as the program spells it
    — "/tmp/out.gif" — is what lets the three modeled operations reach
    the EXISTING arms: the descriptor a create hands out is an ordinary
    `FdFileW` on that key, and read, write, lseek, fstat and close on it
    are the same arms every file uses.  A relative key can
    never collide with one of these, because no key of a relative name
    begins with "/".

    The prefix is five bytes: '/', 't', 'm', 'p', '/'.  Only
    `Fs.Namei.tmp_name` takes it apart again, and only for a path that
    has exactly ONE further component. -/
def tmp_prefix : Fs.path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 116, BitVec.ofInt 8 109,
   BitVec.ofInt 8 112, BitVec.ofInt 8 47]

/-- The flat-map key of the /tmp entry named `name`. -/
def tmp_key (name : Fs.path) : Fs.path := tmp_prefix ++ name

/-- A name with a NUL byte in it is not a name: `read_cstr` stops at the
    first NUL, so no pathname a program can pass names such an entry,
    and Linux's directory entries cannot hold one either.  A declaration
    that mentions one describes nothing, and `fs_seed_tmp` drops it.
    Dropping it is also what keeps the seeded image inside
    `Fs.valid_fs`, whose second clause is exactly this test — see
    `fs_seed_tmp_valid`. -/
def tmp_nul_free (name : Fs.path) : Bool :=
  !(name.any (fun b => bv_eqb b (BitVec.ofInt 8 0)))

/-- Seed a declared private /tmp into a file-system image: insert each
    declared entry under its absolute key, ONE AT A TIME, through the
    file system's own `Fs.fs_set`.

    INSERTION RATHER THAN CONCATENATION IS THE WHOLE POINT.  `Fs.fs_set`
    puts a key in its sorted place and replaces a duplicate, so the
    result is in the canonical form for EVERY list the declaration
    happens to be — unsorted, with repeats, in any order — and the
    declaration therefore needs no validity clause of its own.  That is
    what makes `State.in_tmp` a true input: every value is one a launch
    could present, and
    `Run.valid_input` excludes none of them (`fs_seed_tmp_valid` is the
    proof).  A later entry wins over an earlier one with the same name,
    which is the only reading a fold can give and costs nothing: the two
    describe the same directory entry. -/
def fs_seed_tmp (fs : Fs.Fs) (t : Fs.Fs) : Fs.Fs :=
  List.foldl
    (fun acc e =>
       if tmp_nul_free e.1 then Fs.fs_set acc (tmp_key e.1) e.2
       else acc)
    fs t

theorem fs_seed_tmp_nil (fs : Fs.Fs) : fs_seed_tmp fs [] = fs := rfl

theorem tmp_prefix_nul_free : (BitVec.ofInt 8 0) ∉ tmp_prefix := by decide

theorem tmp_key_nul_free (name : Fs.path) (hn : tmp_nul_free name = true) :
    (BitVec.ofInt 8 0) ∉ tmp_key name := by
  intro hin
  rw [tmp_key, List.mem_append] at hin
  rcases hin with hin | hin
  · exact tmp_prefix_nul_free hin
  · have hc : name.any (fun b => bv_eqb b (BitVec.ofInt 8 0)) = true := by
      rw [List.any_eq_true]
      exact ⟨BitVec.ofInt 8 0, hin, by simp [bv_eqb]⟩
    simp only [tmp_nul_free, hc, Bool.not_true] at hn
    exact Bool.noConfusion hn

/-- THE CLAUSE ON THE IMAGE EXCLUDES NO /tmp.  Seeding a canonical image
    with ANY declared /tmp leaves it canonical, so `Run.valid_input`'s
    `Fs.valid_fs` clause — which reads the SEEDED image, through
    `in_fs` — is satisfied for every value of `in_tmp` whenever it was
    satisfied by the image alone.  That is the precise sense in which
    the declaration is unconstrained: no /tmp table a launch could
    present is ruled out. -/
theorem fs_seed_tmp_valid (t : Fs.Fs) :
    ∀ (fs : Fs.Fs), Fs.valid_fs fs → Fs.valid_fs (fs_seed_tmp fs t) := by
  induction t with
  | nil => intro fs hv; exact hv
  | cons hd t ih =>
    intro fs hv
    obtain ⟨name, data⟩ := hd
    obtain ⟨hs, hf⟩ := hv
    by_cases hn : tmp_nul_free name = true
    · have hstep : fs_seed_tmp fs ((name, data) :: t) =
          fs_seed_tmp (Fs.fs_set fs (tmp_key name) data) t := by
        simp only [fs_seed_tmp, List.foldl, hn, ite_eq_left]
      rw [hstep]
      exact ih (Fs.fs_set fs (tmp_key name) data)
        ⟨Fs.fs_set_sorted fs (tmp_key name) data hs,
         Fs.fs_set_keys (fun q => (BitVec.ofInt 8 0) ∉ q) fs (tmp_key name) data hf
           (tmp_key_nul_free name hn)⟩
    · have hstep : fs_seed_tmp fs ((name, data) :: t) = fs_seed_tmp fs t := by
        simp only [fs_seed_tmp, List.foldl, ite_eq_right hn]
      rw [hstep]
      exact ih fs ⟨hs, hf⟩

/-- The seeding's insertion-closure, the shape `Fs.fs_set_keys` has for
    ONE insertion: a property that holds of every key of the image and
    of every /tmp key holds of every key of the seeded image.  The
    NUL-free clause of `fs_seed_tmp_valid` just above is one instance
    (left as it stands, so that proof keeps reading in one piece);
    `seeded_absolute_key_is_tmp` below is the other. -/
theorem fs_seed_tmp_keys (P : Fs.path → Prop) (t : Fs.Fs) :
    ∀ (fs : Fs.Fs), (∀ pf ∈ fs, P pf.1) → (∀ n, P (tmp_key n)) →
      ∀ pf ∈ fs_seed_tmp fs t, P pf.1 := by
  induction t with
  | nil => intro fs hfs _ pf hpf; exact hfs pf hpf
  | cons hd t ih =>
    intro fs hfs hk pf hpf
    obtain ⟨name, data⟩ := hd
    by_cases hn : tmp_nul_free name = true
    · have hstep : fs_seed_tmp fs ((name, data) :: t) =
          fs_seed_tmp (Fs.fs_set fs (tmp_key name) data) t := by
        simp only [fs_seed_tmp, List.foldl, hn, ite_eq_left]
      rw [hstep] at hpf
      exact ih (Fs.fs_set fs (tmp_key name) data)
        (Fs.fs_set_keys P fs (tmp_key name) data hfs (hk name)) hk pf hpf
    · have hstep : fs_seed_tmp fs ((name, data) :: t) = fs_seed_tmp fs t := by
        simp only [fs_seed_tmp, List.foldl, ite_eq_right hn]
      rw [hstep] at hpf
      exact ih fs hfs hk pf hpf

/-- WHERE AN ABSOLUTE KEY IN A RUN'S FILE SYSTEM CAN COME FROM: the
    seeding, and nothing else.

    Under `Fs.fs_keys_relative` on the image, every key of the seeded
    image is either RELATIVE — it came from the image, and the image's
    keys begin with no "/" — or it is a key the seeding minted, and
    every one of those is `tmp_key n` for the declared name `n`, which
    begins with "/tmp/".  The two halves are one disjunction rather than
    two lemmas because that is how the consumers read it: a spec holding
    an absolute path asks "could this be a key?", and the answer is "only
    if it is under /tmp".

    This is the lemma `Run.device_paths_never_seeded` turns into the
    statement that the device arms' image guards cannot fire on a valid
    input. -/
theorem seeded_absolute_key_is_tmp (t fs : Fs.Fs) (hrel : Fs.fs_keys_relative fs) :
    ∀ pf ∈ fs_seed_tmp fs t,
      Fs.key_is_relative pf.1 ∨ ∃ n, pf.1 = tmp_key n :=
  fs_seed_tmp_keys (fun q => Fs.key_is_relative q ∨ ∃ n, q = tmp_key n) t fs
    (fun pf hpf => Or.inl (hrel pf hpf))
    (fun n => Or.inr ⟨n, rfl⟩)

/- =========================================================================
   The run's input
   ========================================================================= -/

/-- What the CALLER supplies to a run: the argv and envp strings, the
    initial file-system image, the standard-input stream, the user and
    group the process runs as, and the network the program faces.
    `in_stdin` and `in_net` are inputs of the run exactly like the other
    five — colists fixed up front, see `InputStream` and `NetQueue`.
    One record rather than an argument each, so that a new process input
    is a new field here and no consumer's arity moves.

    THE ADVERSARIAL PEER IS AN INPUT, not an internal choice, and that
    is forced rather than stylistic.  `Checks.ExecutableSpecs` proves
    `check_syscall_err_iff` against a TOTAL checker, which makes an arm
    that both succeeds and declines at the same `(i, m)` impossible: one
    `Unmodeled` there forbids every `Ok` there.  Environment choice
    therefore has to arrive quantified, and quantifying it universally
    is also the anti-vacuous direction — `Equivalence.strong_equiv`
    ranges over all inputs, so a new field adds a `forall`, never an
    `exists`.  `Run.valid_input` is the record's validity predicate.

    `in_net` carries no validity clause, and that is a property of the
    REPRESENTATION rather than an omission: `NetStream`'s payload is a
    `byte` and its terminals are nullary, so every value of the type is
    a network a process could really face.

    `in_uid`, `in_gid`, `in_groups` and `in_nofile` are the ENVIRONMENT's
    choice in the same sense the ASLR'd stack pointer and program break are
    (`Run.valid_sp`, `Run.valid_brk`): the model does not know which
    user launched the process, so it quantifies over every user it could
    have been rather than picking one.  A process launched by uid 1001 and the same
    process launched by root are both runs of this model, and a program
    whose observable behavior depends on which is which can only be
    proved equivalent to a target that depends on it the same way.
    Unlike the sp and the break, which are quantified INDEPENDENTLY per
    binary, the process input is SHARED between source and target
    (`Equivalence.strong_universal_T`), so the two binaries always agree
    on who they are.

    The effective and saved ids are NOT separate inputs: `init_model`
    derives them, because `execve` of an ordinary binary leaves the real
    ids alone and sets the saved ids from the effective ones.  Deriving
    rather than carrying is what confines the model to launches whose
    effective ids equal their real ones — such a launch cannot be
    EXPRESSED, there being no field to express it in.  This is not
    `Run.valid_creds`'s doing; that predicate only bounds the two ids to
    32 bits and excludes `(uid_t)-1`.  What is excluded is a secure-exec
    (a set-user-id binary, or one carrying file capabilities), which
    sends libc down its secure-exec path, whose syscalls are outside
    `Specs.modeled_sysnos`.  See `StackLayout.auxv_entries`, which
    relies on the same restriction.

    `in_uid` REACHES THE PROCESS TWICE, and that is the point: `init_model`
    below copies it into `Creds`, which the id readers project, and
    `Run.init_machine_state` hands it to `StackLayout.auxv_entries`,
    which writes it into AT_UID and AT_EUID on the initial stack.  One
    field, so the two answers cannot disagree — as they cannot on Linux,
    where `create_elf_tables` and `SYSCALL_DEFINE0(getuid)` both munge
    `current_cred()->uid`.  `in_gid` reaches only the credentials: this
    auxv carries no AT_GID or AT_EGID entry at all, so there is no
    second group answer for it to contradict.

    `in_groups` is an input for the same reason, and it is an input
    rather than a constant because the kernel never resets it: `execve`
    builds the new credentials with `prepare_exec_creds`, which adjusts
    the keyrings and the saved/fs ids and leaves `group_info` alone, and
    the `prepare_creds` underneath it carries the SAME `struct
    group_info` over by `memcpy` plus `get_group_info` (kernel/cred.c,
    reached from fs/exec.c's `bprm` credential setup; v6.10..v6.18).  So
    the list a process starts with is whatever its parent had, and no
    syscall this model admits can change it — `setgroups` (159) is
    -EPERM unprivileged and declined privileged.  It is therefore
    CONSTANT over a modeled run, which is why `Creds` can hold it and
    nothing has to write it back.

    `in_nofile` is an input for the same reason, and CONSTANT for a
    reason worth stating precisely, because an exec really can change
    this limit: the LSM `bprm_committing_creds` hooks clamp every
    resource including NOFILE (security/selinux/hooks.c,
    `selinux_bprm_committing_creds`; security/apparmor/resource.c; Linux
    v6.18.46, commit 1f99e9ab748f).  What makes the field constant is
    not that nothing writes it but WHEN the writers run — at exec, at
    boot, on a core dump — and this model begins AT execve and reaches
    none of them afterwards.  So the limit a run starts with is the one
    it ends with, and where it came from is the environment's business.
    `limst_nofile` carries the rest of the argument, over the syscalls
    this model does admit.  Unlike `in_groups` it DOES carry a `Run.valid_input`
    clause, and the difference is which end bounds it: an over-long group
    list is refused where it is read, while the descriptor limit is
    ANSWERED from, so an unreachable value would be answered rather than
    declined.  `Run.valid_nofile` carries that bound and its kernel
    argument.

    The consumers — `init_model` here, `Run.init_config` and `Run.run` —
    take the record whole and read the fields with the record
    PROJECTIONS rather than by matching on it.  A projection reduces
    whatever the record is, so `m_fs (init_model _ _ _ _ inp) = in_fs inp`
    holds by `rfl` for a variable `inp`, where a match would be
    stuck, and a literal `mkProcInput` still iota-reduces through the
    projections to its fields. -/
structure ProcInput where
  mkProcInput_full ::
  in_argv : List (List byte)
  in_envp : List (List byte)
  /-- the file-system image the run is launched over, WITHOUT the
      run's private /tmp.  Read it through `in_fs` below, which is
      what every consumer means by "the file system the run starts
      with"; this projection exists so that the image and the
      declared /tmp can be supplied separately -/
  in_image_fs : Fs.Fs
  in_stdin : InputStream
  /-- the real user id the process is launched with -/
  in_uid : word
  /-- the real group id the process is launched with -/
  in_gid : word
  /-- the supplementary group list the process is launched with, in the
      kernel's stored order — see `Creds`'s `cr_groups`, which
      `init_model` copies this into -/
  in_groups : List word
  /-- the connections the environment offers, and what each peer says
      once accepted — see `NetQueue` and `NetStream` -/
  in_net : NetQueue
  /-- the SOFT RLIMIT_NOFILE the process is launched with, an
      `unsigned long` — see `LimState`'s `limst_nofile`, which
      `init_model` copies this into, and `Sys.Fs.File.dup3_spec`, its
      one reader.  `Run.valid_nofile` bounds it -/
  in_nofile : word
  /-- the signals BLOCKED at the moment the process starts, as riscv64's
      one-word `sigset_t`.  An input for the same reason `in_uid` is:
      execve does not reset `task_struct.blocked` — `fs/exec.c` never
      names the field and `begin_new_exec` resets DISPOSITIONS only,
      via `flush_signal_handlers` (Linux v6.18.46, commit
      1f99e9ab748f) — so the starting mask is whatever launched the
      process, and the model cannot derive it.  `Run.valid_input`
      constrains it; see `valid_sigmask` there for what and why -/
  in_sigmask : word
  /-- the AT_HWCAP word the auxv publishes: which single-letter ISA
      extensions the HART this process runs on implements.  An input
      rather than a constant because the model has no term for the
      machine — the same reason `riscv_hwprobe` stays outside
      `Specs.modeled_sysnos`.  `Run.valid_hwcap` narrows it to the two
      masks a hart that can run this model's instructions may publish;
      `StackLayout.auxv_entries` is its one reader, and the AT_HWCAP
      bullet there carries the kernel argument for the pair -/
  in_hwcap : word
  /-- THE TASK'S DECLARATION, and the one field of this record that is
      not a fact about the environment: whether the model covers the
      abort path -- `tkill` (130), `tgkill` (131) and the fatal SIGABRT
      they can leave pending -- or declines it.
      `Run.valid_input` pins it to `false`; a task that
      wants the other stance quantifies over `Run.valid_input_abort`
      instead, and a statement that pins neither asserts both.

      IT IS HERE RATHER THAN BESIDE `Run.SpuriousCfg` because it decides
      what a SPEC admits rather than which of a spec's outcomes survive,
      and a spec's only channel to the run's parameters is the model
      (`procst_abort_terminal`, which `init_model` copies this into and
      nothing else writes).  What it buys by being a field of the input
      is that it lands in the statement's quantifier for free, which is
      where a reader has to be able to see it -/
  in_abort_terminal : Bool
  /-- THE TASK'S DECLARATION of the kernel's user address-space size --
      which page-table depth the machine this process runs on booted
      with -- and, like the credentials, a fact about the environment
      the model cannot derive: nothing a trace reveals says whether the
      kernel was Sv39, Sv48 or Sv57, and the answer changes where the
      stack is and which addresses `access_ok` admits.  `Run.valid_input`
      pins it to `Sv48`, the size every statement in this tree is
      written against; the per-size variants beside it pin the others,
      and `Run.valid_entry` reads it to choose the window.  The
      paragraph above `VaSize` says what the declaration decides today
      and what it does not.

      It is NOT copied into the model: no spec arm reads it (they read
      `TASK_SIZE`), and `Equivalence.strong_equiv_va` is where a
      statement under a size the arms do not implement is refused.
      The day an arm reads the declared size, this field is seeded into
      the model the way `in_nofile` is, and that note is the one to
      update -/
  in_va_size : VaSize
  /-- THE ENVIRONMENT'S DECLARATION of the bytes the random device
      hands out, in order: what every read of /dev/urandom
      (`Fs.Open.openat_urandom_spec`, `State.FdUrandom`) delivers,
      front first, across every descriptor the run opens on it.  Like
      `in_va_size` it is a fact about the environment the model cannot
      derive -- nothing a trace reveals says which bytes the kernel's
      generator produced -- and like `in_stdin` it is an INPUT of the
      run rather than an internal choice: the stream is ARBITRARY BUT
      FIXED, a parameter of the execution exactly as argv and envp
      are, so a program's behaviour is a function of it and every
      equivalence is proved for every stream, with the SAME stream
      seen by the source and the target of a pair.  It is not
      nondeterministic in the model, and it is not `getrandom`'s
      source: `Drivers.Char.Random.getrandom_spec` keeps its own
      `choose`.  `Run.valid_urandom` is the ONE clause on it, and it
      says only that the declared stream never ends: a short read from
      this device is not a thing Linux does, so a finite declaration
      describes no device at all.  It is not the clause `in_stdin`
      does without -- a pipe that ends is a real pipe -- and it says
      nothing whatever about WHICH bytes come out.  `init_model` seeds
      `iost_urandom` from it, and the read arm consumes that copy the
      way stdin's arm consumes `iost_stdin`. -/
  in_urandom : InputStream
  /-- THE ENVIRONMENT'S DECLARATION of the run's PRIVATE /tmp at
      launch: the files it already contains, keyed by the ONE
      component of their name (no "/tmp/" prefix in the key).  Like
      `in_urandom` it is a fact about the environment the model cannot
      derive, and like it the value is ARBITRARY BUT FIXED -- a
      parameter of the execution exactly as argv and envp are, the
      SAME directory seen by the source and the target of a pair, so
      every equivalence is proved for every declared /tmp.  It is not
      nondeterministic in the model.

      THE PREMISE IT CARRIES is that /tmp is a distinct, writable
      directory PRIVATE to this run, which is what makes this table
      the whole truth about it: what the run holds there is this
      declaration, plus what `Fs.Open.create_wronly` created, minus
      what `Fs.Namei.unlinkat_spec` removed, and nothing else can put
      a file there or take one away.

      `Run.valid_input` has NO clause naming it: `fs_seed_tmp` seeds
      any list into the canonical form, so every value is one a launch
      could present (`fs_seed_tmp_valid`). -/
  in_tmp : Fs.Fs

/-- THE POSITIONAL-LITERAL FORM: every field except the two ENVIRONMENT
    fields at the end of the record (`in_urandom`, `in_tmp`).

    The record's own constructor is `mkProcInput_full` and takes every
    field.  This takes the first thirteen, in that order,
    and fills the last two with THE DEFAULT RANDOM STREAM and
    THE EMPTY /tmp: `default_urandom`, which is zero bytes forever, and
    a private /tmp that starts empty.  So a literal written through this
    name denotes an input in an environment
    that holds no file of its own.

    THE RANDOM DEFAULT IS NOT `IEof`: under
    `Run.valid_urandom` every valid input declares an endless stream, so
    a fixture built here with `IEof` would fail its own validity pin.

    WHY IT EXISTS: consumers of this specification hold positional
    `mkProcInput` literals in numbers, and a field added to the middle
    of the record silently changes what such a literal means while a
    field added to the end merely breaks it.  Keeping the thirteen-place
    form under this name, and putting every new environment field at
    the END, is what makes an added field a compile error there rather
    than a re-spelling of every literal.  A NEW literal that wants to
    set either field uses `mkProcInput_full` or the record-brace form;
    this one cannot express them, which is the point.

    It is a plain (transparent) `def`, so it reduces wherever the
  constructor would — but a `simp` or `simpl` with an explicit
    constant list has to name it to see through it. -/
def mkProcInput
    (argv envp : List (List byte)) (image_fs : Fs.Fs) (stdin : InputStream)
    (uid gid : word) (groups : List word) (net : NetQueue)
    (nofile sigmask hwcap : word) (abort_terminal : Bool)
    (va_size : VaSize) : ProcInput :=
  ProcInput.mkProcInput_full argv envp image_fs stdin uid gid groups net
    nofile sigmask hwcap abort_terminal va_size default_urandom []

/-- THE FILE SYSTEM THE RUN STARTS WITH: the image, with the run's
    declared private /tmp seeded into it under absolute keys.

    This is what every consumer means by `in_fs`, and it is
    what `init_model` installs, so `m_fs (init_model _ _ _ _ _
    inp) = in_fs inp` holds by `reflexivity`.  The record carries the
    image and the
    declared /tmp as two fields, and this function is the one place
    that puts them together.

    IT IS A FUNCTION RATHER THAN A PROJECTION, which the record's header
    note above asks about: a function of two projections reduces exactly
    as a projection does for a variable `inp`, so the reflexivity
    property the note is written for is unaffected.  An input whose
    `in_tmp` is the empty declaration gives back the image itself
    (`fs_seed_tmp_nil`), by computation, which is why every literal
    built with `mkProcInput` reduces to its image. -/
def in_fs (inp : ProcInput) : Fs.Fs :=
  fs_seed_tmp inp.in_image_fs inp.in_tmp

/- =========================================================================
   Initial model: fds 0/1/2 bound to the three standard channels;
   `reserved` is the address space the kernel used at `execve` (the
   page-rounded LOAD segments, built by `Run.segments_reserved`), which
   the allocator may never grant; `brk0` is the ASLR-placed initial
   program break (`Run.valid_brk` — quantified per binary like the
   initial SP, see `Run.mi_init_brk`); `mbase` is the layout-placed
   `mm->mmap_base` (`Run.valid_mmap_base` — quantified the same way,
   see `Run.mi_mmap_base` and the `vm_mmap_base` field note); `sp` is
   the initial stack pointer (`Run.valid_sp`, see `Run.mi_init_sp` and
   the `vm_init_sp` field note), which `alloc_top` bounds every grant
   by; the file
   system, standard
   input and the random device's stream start as the `in_fs`, `in_stdin`
   and `in_urandom` of the caller-supplied
   `inp`, read through the record projections (see `ProcInput`); `lim`
   is the run's backed anonymous-memory budget in bytes (`vm_limit` — see the
   field's note and its companion constants
   `source_alloc_limit`/`target_alloc_limit`).

   The six CREDENTIAL ids are built from the two the input carries.
   `execve` of an ordinary binary — one that is neither set-user-id nor
   set-group-id and carries no file capabilities — leaves the real ids
   untouched, keeps the effective ids of the calling process, and then
   sets the saved set-ids and the filesystem ids from the effective ones
   (Linux v6.18.46, commit 1f99e9ab748f, security/commoncap.c,
   `cap_bprm_creds_from_file`, whose
   `new->suid = new->fsuid = new->euid;` and
   `new->sgid = new->fsgid = new->egid;` run on every exec, setuid or
   not.  Those two lines are byte-identical from v6.10 through v6.18;
   the function around them is not, because v6.17 rewrote the test that
   marks an exec privilege-elevated, but every term it added compares an
   effective id with a real one, and a launch whose two differ is not an
   input `ProcInput` can express.  kernel/cred.c, `prepare_exec_creds`,
   does the same earlier).
   Because `ProcInput` carries no effective id, all three collapse to
   the one value the input supplies, and a secure-exec — whose
   effective id differs — is not an input this model can state.
   ========================================================================= -/

/-- The model a run starts from.  See the section header above for what
    each of `reserved`, `brk0`, `mbase`, `sp` and `lim` is, and why the
    credentials are derived from the input's two ids rather than taken
    from it. -/
def init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) : Model :=
  with_abort_terminal (inp.in_abort_terminal)
  (with_sigmask (inp.in_sigmask)
  (with_nofile (inp.in_nofile)
   (with_net (inp.in_net)
   (with_urandom (inp.in_urandom)
   (with_creds
    (Creds.mkCreds (inp.in_uid) (inp.in_uid) (inp.in_uid)
             (inp.in_gid) (inp.in_gid) (inp.in_gid) (inp.in_groups))
    (mkModel
       [ (BitVec.ofInt 64 0, FdEntry.FdChannel (BitVec.ofInt 64 0)),
         (BitVec.ofInt 64 1, FdEntry.FdChannel (BitVec.ofInt 64 1)),
         (BitVec.ofInt 64 2, FdEntry.FdChannel (BitVec.ofInt 64 2)) ]
       (VmMaps.mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
       (inp.in_stdin)
       (in_fs inp)
       none
       none
       none))))))

/-- The base case of the nonemptiness invariant: a run starts with NO
    protected range at all.  Every reachable `vm_noaccess` is therefore
    reached from `[]` by the writers in `Mm/Mmap.lean` and
    `Mm/Mprotect.lean`, each of which is shown there to preserve
    `vm_noaccess_entries_nonzero`. -/
theorem init_model_noaccess_nonzero (reserved : List (word × word))
    (brk0 mbase sp : word) (lim : Int) (inp : ProcInput) :
    vm_noaccess_entries_nonzero (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) := by
  unfold vm_noaccess_entries_nonzero
  exact entries_nonzero_nil

/- =========================================================================
   Sanity checks

  the ones below pin the parts of chunk B8 that are decidable: the seeded `/tmp`
  round-trips through `Fs.fs_lookup`, and `init_model` installs the three standard
  descriptors, the seeded image, no halt, and the input's descriptor limit.
   ========================================================================= -/

/-- A FULLY CONCRETE INPUT: no argv, no envp, an empty image, an empty
    stdin, uid/gid 1000 with no supplementary groups, the silent accept
    queue, the ordinary 1024-descriptor limit, nothing blocked, no hwcap,
    the abort path declined, Sv48 — and ONE declared `/tmp` file, named
    `tmp` (three bytes, not the four of the prefix), holding `1,2,3`.

    A Lean-side fixture for the checks below; -/
def check_input : ProcInput :=
  { mkProcInput [] [] [] IEof 1000 1000 [] net_silent
      (BitVec.ofInt 64 1024) 0 0 false VaSize.Sv48 with
    in_tmp := [([116, 109, 112], [1, 2, 3])] }

/-- The seeding puts the declared entry under its absolute key, and
    `Fs.fs_lookup` finds it there (`fs_seed_tmp`, `tmp_key`, `in_fs`). -/
example : Fs.fs_lookup (in_fs check_input) [47, 116, 109, 112, 47, 116, 109, 112] =
    some [1, 2, 3] := by decide

/-- ... under the key `tmp_key` mints, spelled out byte by byte: the five
    bytes of "/tmp/" then the declared name. -/
example : tmp_key [116, 109, 112] = [47, 116, 109, 112, 47, 116, 109, 112] := by decide

/-- A name with a NUL byte in it IS dropped, so it names nothing in the
    seeded image (`tmp_nul_free`, `fs_seed_tmp`). -/
example : Fs.fs_lookup
    (in_fs { check_input with in_tmp := [([110, 0, 108], [9])] })
    [47, 116, 109, 112, 47, 110, 0, 108] = none := by decide

/-- An empty declaration gives back the image itself (`fs_seed_tmp_nil`). -/
example : in_fs { check_input with in_tmp := [] } = [] := by decide

/-- The three standard descriptors are channels, in order, whatever the
    input is: `init_model` writes that table unconditionally. -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_fds (init_model reserved brk0 mbase sp lim inp) =
      [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1),
        (2, FdEntry.FdChannel 2) ] := rfl

/-- The file system is the SEEDED one, by computation: this is the
    `reflexivity` property `ProcInput`'s header note is written for, and
    it holds for a variable `inp`. -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) : m_fs (init_model reserved brk0 mbase sp lim inp) = in_fs inp := rfl

/-- A run starts running: `m_halted` is `none`, and therefore
    `m_killed` is too. -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) : m_halted (init_model reserved brk0 mbase sp lim inp) = none := rfl

example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) : m_killed (init_model reserved brk0 mbase sp lim inp) = none := rfl

/-- The descriptor limit is the INPUT's, not `default_nofile`
    (`with_nofile`). -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_nofile (init_model reserved brk0 mbase sp lim inp) = inp.in_nofile := rfl

/-- The random device's stream is the input's, and it is not `IEof` for a
    literal built by `mkProcInput` (`with_urandom`, `default_urandom`). -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_urandom (init_model reserved brk0 mbase sp lim inp) = inp.in_urandom := rfl

/-- The credentials are the input's two ids, EACH REPEATED THREE TIMES:
    real, effective and saved collapse to one value because a secure-exec
    is not expressible (`Creds.mkCreds`). -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_creds (init_model reserved brk0 mbase sp lim inp) =
      Creds.mkCreds inp.in_uid inp.in_uid inp.in_uid
        inp.in_gid inp.in_gid inp.in_gid inp.in_groups := rfl

/-- The initial ledger's immutable parameters come straight from the
    arguments — the reserved image, the budget and the stack pointer —
    and both the mapping list and the protected range start EMPTY, which
    is what `init_model_noaccess_nonzero` reads (`mkVmMapsFull`). -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_reserved = reserved ∧
      (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_limit = lim ∧
      (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_init_sp = sp ∧
      (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_maps = [] ∧
      (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_noaccess = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The declared `/tmp` reaches the model's image through `in_fs`. -/
example :
    Fs.fs_lookup (m_fs (init_model [] 0 0 0 0 check_input)) [47, 116, 109, 112, 47, 116, 109, 112] =
      some [1, 2, 3] := by decide

/-- ... and a run started from `check_input` really is unprivileged:
    uid 1000 repeated. -/
example : creds_privileged (m_creds (init_model [] 0 0 0 0 check_input)) = false := by decide

/- =========================================================================
   Carried from State.lean:5402–5416, the block that heads chunk B9:

   (** * The setter/accessor interactions, as REWRITES rather than
       reductions.

       Reducing through these with explicit constant lists
  ([`simp` [with_fds m_fds...]]) does not work on the nested [Model]:
       such a list has to name every
       constant on the way from [m_fds (with_fds x m)] down to [x], and
       naming them ALSO unfolds a bare [m_fs model] --
       which later steps match on literally, and then cannot find.

       So the accessors and setters are opaque to reduction (below) and these
       lemmas are how a proof gets through them.  Every one is [reflexivity]:
       the nesting is definitional, and this only decides which shapes a proof
       is allowed to see.  Registered in the [model] database, so a caller
  writes [`simp`] and names no field. *)
   ========================================================================= -/

end LinuxSem.LinuxProcessSem
