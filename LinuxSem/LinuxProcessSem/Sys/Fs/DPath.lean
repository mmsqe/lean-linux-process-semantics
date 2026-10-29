/-
  * LinuxProcessSem.Sys.Fs.DPath — getcwd (17)

  This file answers to Linux `fs/d_path.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  here that is `SysSpec SyscallEffect` from `MonadInstances`. The `sys_scope`
  sequencing `x <- c;; k` is `bind c (fun x => k)` in Lean, which is how the one
  `errno_from` step below is written. `ret_only`, `err_ret` and `errno_from` are
  `Sys/Syscall.lean`'s; `alt` and `unmodeled` are `Monad.lean`'s, re-exported through
  `MonadInstances`.

  guard is
  `if (1 <? bv_unsigned size)%Z` — a `Z` comparison against the UNSIGNED
  reading of the register.  The port spells that reading `size.toNat`, the
  `Nat` holding the same value, so the guard is `1 < size.toNat` and the
  band it guards is `size.toNat ≤ 1`.  `bv_unsigned` is never negative and
  `toNat` is never negative, so the two bands agree exactly on every
  register value, `2^64 - 1` included.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.Sys.Syscall

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.DPath

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall

/-- getcwd's injectable failures: the three answers that depend on
    kernel or file-system state this model does not carry, all of them
    decided BEFORE the size comparison and therefore live on every arm
    below.

    - ENOMEM — `__getname()`, the very first statement, is a
      `GFP_KERNEL` allocation out of `names_cachep` and can fail.  It
      is the only error that returns without the RCU section running
      at all.
    - ENOENT — `d_unlinked(pwd.dentry)`: the caller's working directory
      has been removed from the dcache hash and is not its own root.
      Another process rmdir'ing the directory this one sits in produces
      it.  Note it is NOT the unreachable case: a working directory
      outside the caller's root is a SUCCESS returning a string prefixed
      "(unreachable)".
    - ENAMETOOLONG — the assembled path did not fit `PATH_MAX`, which
      `prepend`/`prepend_char` signal by driving the buffer's `len` to
      -1.  Reachable by nesting directories with relative `mkdir`s until
      the absolute path exceeds 4096 bytes.

    (Linux v6.18.46, commit 1f99e9ab748f, fs/d_path.c,
    `SYSCALL_DEFINE2(getcwd)`.)

    EFAULT is deliberately absent: it can only be reached AFTER the size
    comparison, which the modeled band below never gets past. -/
def getcwd_errnos : List Int := [ENOMEM, ENOENT, ENAMETOOLONG]

/-- `getcwd buf size`: copy the caller's working directory out, and
    return its length INCLUDING the terminating NUL (not 0 — the comment
    above `SYSCALL_DEFINE2(getcwd)` states the convention, and line
    `error = len;` is where it happens).

    THERE IS NO WORKING DIRECTORY IN THIS MODEL, and that is a fact
    about the representation rather than a gap in the bookkeeping.
    `State.Model` has no pwd field; `Fs.Fs` is a flat association list
    from an UNINTERPRETED byte-string path to that file's bytes, with no
    root, no directories and no resolution; and every modeled path-taking
    syscall (`Fs.Open.openat_spec`, `Fs.Stat.newfstatat_spec`,
    `Fs.Namei.unlinkat_spec`) declines any dirfd but AT_FDCWD and then
    looks the name up in that map directly.  So the working directory is
    not an untracked value that could be threaded through later — there
    is no term in the model a directory could be, and the string getcwd
    would return is not a function of any modeled state.  Every outcome
    that would carry that string is therefore `unmodeled`, fail closed.
    (This paragraph stops being true the moment `Fs` grows directories
    and `State.Model` a pwd field: at that point the success arm and the
    -EFAULT arm below it become derivable and the decline should go.)

    WHAT IS LEFT IS THE BAND WHERE THE WORKING DIRECTORY CANNOT MATTER.
    Call `len` the quantity the kernel compares against `size` and
    returns on success.  For `size <= 1`, `len > size` holds for EVERY
    possible working directory, so no success and no -EFAULT is
    reachable and the answer is -ERANGE or one of the three injectable
    errnos above.  The argument, in the kernel's own order, reading
    `SYSCALL_DEFINE2(getcwd)`, `prepend_path`, `__prepend_path`,
    `prepend`, `prepend_char` and `prepend_name` in Linux v6.18.46,
    commit 1f99e9ab748f, fs/d_path.c:

    - `DECLARE_BUFFER(b, page, PATH_MAX)` starts `b.len` at PATH_MAX.
    - `prepend_char(&b, 0)` writes the terminating NUL first, taking
      `b.len` to PATH_MAX - 1.
    - `prepend_path` either OVERFLOWS — `prepend`/`prepend_char` set
      `b.len` to -1 — or returns having consumed at least one more byte:
      its tail is `if (b.len == p->len) prepend_char(&b, '/');`, so a
      working directory equal to the root still costs the "/".  Hence
      `b.len <= PATH_MAX - 2` on every non-overflow path.  That step
      needs `b.len` never to RISE, since the "/" fires only on
      equality.  For a non-negative `namelen`, `prepend` and
      `prepend_char` only ever lower it or set it to -1, and
      `prepend_path`'s own two writes — `b = *p` at `restart:`, and the
      same assignment again when `__prepend_path` answered 3 — restore
      it to exactly `p->len` rather than above it.
      So the only input that could raise it is a NEGATIVE `namelen`:
      `prepend_name` reads a `u32 dlen` out of `d_name.len` and passes
      it into `prepend`'s `int`, so a length at or above 2^31 would
      make `p->len -= namelen` increase `p->len` instead.  `struct
      qstr` carries no bound of its own, and neither does the path walk
      — fs/namei.c has no NAME_MAX check at all, which `Uapi.NAME_MAX`
      already records and `Namei.unlinkat_spec` already leans on.  The
      bound that does hold is the ALLOCATION's, and it covers every
      dentry however the name was built: `__d_alloc` (fs/dcache.c)
      stores it inline or through a `kmalloc` sized from `name->len`,
      and KMALLOC_MAX_SIZE is 4 MiB on riscv64 (MAX_PAGE_ORDER 10,
      PAGE_SHIFT 12), so a 2^31-byte name fails the allocation instead
      of reaching a dentry.  The one name written outside `__d_alloc` —
      `d_mark_tmpfile`'s `sprintf` of an inode number into the inline
      buffer — is bounded by its own format.  A merely LARGE `dlen` is
      harmless in any case: `prepend` takes its overflow branch,
      `b.len` becomes -1, and the `len > PATH_MAX` guard below catches
      it.  Only a `dlen` at or above 2^31 would put `len` below 2
      without tripping that guard, and no dentry can hold one.
    - `len = PATH_MAX - b.len`, so `len >= 2` when the buffer held, and
      `len = PATH_MAX + 1` when it did not.
    - the overflow is caught FIRST, by `if (len > PATH_MAX) error =
      -ENAMETOOLONG;`, so `len > size` is only ever evaluated with
      `len` in [2, PATH_MAX].

    So `size` of 0 or 1 is -ERANGE, whatever the working directory is.
    A working directory outside the caller's root does not weaken this.
    `__prepend_path` answers 1 (absolute root), 2 (detached) or 3
    (escaped mid-walk); getcwd keys on `> 0` rather than on any one of
    them and prepends the 13-byte literal "(unreachable)" for all
    three.  On the 3, `prepend_path` additionally resets the buffer
    (`if (unlikely(error == 3)) b = *p;`) before the "/" test — so
    `len` is exactly 15 there, and at least 15 on the other two.

    ORDER, AND WHAT IT MEANS FOR `buf`.  The kernel's sequence is
    ENOMEM, then ENOENT, then the whole path is built into a KERNEL
    page, then ENAMETOOLONG, then ERANGE, and only then a single
    `copy_to_user`.  There is no `access_ok` and no probe of `buf`
    anywhere earlier.  So `buf` is not an argument of this spec at all
    — a spec that consulted `in_wmem` here would answer -EFAULT where
    Linux answers -ERANGE, and `getcwd(NULL, 0)` really is -ERANGE.
    The -EINVAL that POSIX documents for a zero size is glibc's own and
    never reaches the kernel: `sysdeps/unix/sysv/linux/getcwd.c`
    answers a zero `size` with a non-null `buf` before issuing the
    call, and substitutes PATH_MAX when `buf` is null.  That half is
    not pinned to a glibc version because nothing here rests on it;
    what does is that the syscall body has no -EINVAL arm at all,
    which is read from the fs/d_path.c above.

    Nothing is written on any admitted arm, so the effect is a bare
    return with five empty ledgers.

    -ERANGE and the three injectable errnos are offered as an `alt`
    rather than ranked, because they are not a priority ordering over
    one state: in any single run exactly one of them applies, and which
    one is decided by allocator, dcache and directory-depth conditions
    the model does not carry. -/
def getcwd_spec (size : word) : SysSpec SyscallEffect :=
  if 1 < size.toNat then unmodeled   /- the cwd would decide it: fail closed -/
  else alt (bind (errno_from getcwd_errnos) (fun e => err_ret e)) (err_ret ERANGE)

/-! ## Sanity checks

  It is two definitions and the prose above. The checks below are PORT CHECKS, and
  they pin what the header argues for:

    - the injectable set and the errno encodings;
    - the size-0/size-1 band: `size ≤ 1` admits -ERANGE and each of the
      three injectable errnos, and `size ≥ 2` admits NOTHING (`unmodeled`,
      the fail-closed success arm);
    - the POSIX -EINVAL-for-a-zero-size story is NOT modelled, because the
      kernel has no such arm: `getcwd_spec 0` never returns -EINVAL;
    - nothing is written on any admitted arm — every effect is a bare
      return with the five ledgers empty.

    THE SUCCESS ARM CANNOT BE CHECKED HERE, and that is the point rather
    than a hole in the checks: the "." + NUL string a successful getcwd
    returns is a function of a working directory this model does not
    carry, so the only check the success side admits is the DECLINE —
    `size ≥ 2` is `unmodeled`, never a fabricated string.  A check that
    `getcwd_spec` writes "." and its NUL would be checking a model this
    file deliberately does not have; see the header's "THERE IS NO
    WORKING DIRECTORY IN THIS MODEL". -/

/-- A syscall input for `getcwd` (17).  The spec reads none of it: it is
    here because a `SysSpec` is a relation on an input as well as a
    model.  `in_args` carries the `(buf, size)` pair the dispatcher would
    hand over; `buf` (a0) is not consulted — see the header. -/
private def demoInput : SyscallInput :=
  { in_sysno := 17, in_args := [0, 0], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- The model the checks run in: no fds, an empty VM ledger, an empty file
    system, EOF on stdin, no halt and no rlimit.  Nothing in it can matter
    to getcwd — the spec never looks at the model — which is exactly the
    property the fail-closed arm rests on. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- The bare-return effect for errno `e`: what `err_ret e` produces, with
    all five ledgers empty. -/
private def errEffect (e : Int) : SyscallEffect := mkEffect (errno_ret e) [] []

/-! ### The injectable set and the errno encodings -/

/-- The set is three errnos wide, in the kernel's own order:
    ENOMEM, ENOENT, ENAMETOOLONG. -/
example : getcwd_errnos = [ENOMEM, ENOENT, ENAMETOOLONG] := rfl

/-- …and it is exactly `[12, 2, 36]` in the numbers the kernel uses. -/
example : getcwd_errnos = ([12, 2, 36] : List Int) := by decide

/-- The three injectable errnos in the return word — `a0 = -e` in two's
    complement, the encoding every arm below hands back. -/
example : errno_ret ENOMEM = BitVec.ofInt 64 (-12) := by decide
example : errno_ret ENOENT = BitVec.ofInt 64 (-2) := by decide
example : errno_ret ENAMETOOLONG = BitVec.ofInt 64 (-36) := by decide

/-- …and the two the header argues about: the -ERANGE the small-size band
    answers, and the -EINVAL it does NOT. -/
example : errno_ret ERANGE = BitVec.ofInt 64 (-34) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide

/-! ### The two admitted shapes, as lemmas

    `getcwd_spec` has exactly two shapes, and the lemmas from
    `getcwd_spec_big` to `getcwd_spec_band_ok` are the file in miniature:
    above the band it is `unmodeled` and nothing else; on the band it is a
    bare return with five empty ledgers, of -ERANGE or of one of the three
    injectable errnos.  The `example`s below read them. -/

/-- What a single `err_ret` admits, unfolded: the errno's return word,
    the model unchanged, no events. -/
private theorem err_ret_ok (e : Int) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) :
    err_ret e i m (.ok eff m' evs) ↔
      eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  unfold err_ret ret_only pure
  simp only [Outcome.ok.injEq]

/-- What `errno_from` admits, unfolded: an element of the list, the model
    unchanged, no events.  This is the `choose` half of the injectable
    arm, split out so the spec's own proof does not have to reason
    through the existential. -/
private theorem errno_from_ok (es : List Int) (i : SyscallInput) (m : Model)
    (e : Int) (m1 : Model) (evs1 : List event) :
    errno_from es i m (.ok e m1 evs1) ↔ e ∈ es ∧ m1 = m ∧ evs1 = [] := by
  unfold errno_from choose
  constructor
  · rintro ⟨x, hx, hok⟩
    simp only [Outcome.ok.injEq] at hok
    obtain ⟨rfl, rfl, rfl⟩ := hok
    exact ⟨by simpa using hx, rfl, rfl⟩
  · rintro ⟨hx, rfl, rfl⟩
    exact ⟨e, hx, rfl⟩

/-- `err_ret` never declines: a bare return is an `ok`, not an
    `unmodeled`. -/
theorem err_ret_unmodeled_false (e : Int) (i : SyscallInput) (m : Model) :
    ¬ err_ret e i m .unmodeled := by
  unfold err_ret ret_only pure
  intro h
  cases h

/-- …and neither does `errno_from`: the `choose` always picks something,
    so the injectable arm of the `alt` is never a decline either. -/
private theorem errno_from_unmodeled_false (es : List Int) (i : SyscallInput)
    (m : Model) : ¬ errno_from es i m .unmodeled := by
  unfold errno_from choose
  rintro ⟨x, -, h⟩
  cases h

/-- ABOVE THE BAND THE CALL IS DECLINED, and the decline is total: for
    `size ≥ 2` the spec relates `o` to nothing but `unmodeled`.  This is
    the success arm the model cannot produce — the "." + NUL string is
    not a function of any modeled state — together with the -EFAULT arm
    that would follow it. -/
theorem getcwd_spec_big (size : word) (i : SyscallInput) (m : Model)
    (H : 1 < size.toNat) (o : Outcome SyscallEffect Model event) :
    getcwd_spec size i m o ↔ o = .unmodeled := by
  simp [getcwd_spec, H, unmodeled]

/-- ON THE BAND NOTHING IS DECLINED: neither the `choose` nor the bare
    -ERANGE return admits `unmodeled`, so `size ≤ 1` always answers with
    one of the four errnos. -/
theorem getcwd_spec_band_not_unmodeled (size : word) (H : ¬ 1 < size.toNat)
    (i : SyscallInput) (m : Model) : ¬ getcwd_spec size i m .unmodeled := by
  simp only [getcwd_spec, ite_eq_right H, alt]
  rintro (Hinj | Hrange)
  · simp only [bind] at Hinj
    rcases Hinj with Hc | ⟨x, m1, evs1, Hc, Hk⟩
    · exact errno_from_unmodeled_false _ i m Hc
    · exact err_ret_unmodeled_false x i m1 Hk
  · exact err_ret_unmodeled_false ERANGE i m Hrange

/-- THE TWO TOGETHER: `unmodeled` is exactly the `size ≥ 2` case.  The
    fail-closed convention read in both directions — a decline is never
    an excuse for silence where the kernel's answer is known, and it is
    never a licence to invent one where it is not. -/
theorem getcwd_spec_unmodeled_iff (size : word) (i : SyscallInput) (m : Model) :
    getcwd_spec size i m .unmodeled ↔ 1 < size.toNat := by
  constructor
  · intro Hun
    exact Nat.lt_of_not_le fun h =>
      getcwd_spec_band_not_unmodeled size (Nat.not_lt.mpr h) i m Hun
  · intro h
    exact (getcwd_spec_big size i m h .unmodeled).mpr rfl

/-- EVERY ADMITTED OUTCOME IS A BARE RETURN: the model is left alone, no
    event is emitted, and the effect is the return word of one of the
    four errnos with all five ledgers empty.  This is the "nothing is
    written on any admitted arm" claim of the header, as a theorem — it is
    what makes `buf` legitimately absent from the signature. -/
theorem getcwd_spec_admitted (size : word) (i : SyscallInput) (m : Model)
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : getcwd_spec size i m (.ok eff m' evs)) :
    m' = m ∧ evs = [] ∧
      ∃ e ∈ getcwd_errnos ++ [ERANGE], eff = mkEffect (errno_ret e) [] [] := by
  by_cases hb : 1 < size.toNat
  · exact absurd H (by simp [getcwd_spec_big size i m hb])
  · simp only [getcwd_spec, ite_eq_right hb, alt] at H
    rcases H with Hinj | Hrange
    · rcases Hinj with ⟨e, m1, evs1, evs2, hc, hk, hevs⟩
      rw [errno_from_ok] at hc
      obtain ⟨hmem, rfl, rfl⟩ := hc
      rw [err_ret_ok] at hk
      obtain ⟨heff, rfl, rfl⟩ := hk
      simp only [List.nil_append] at hevs
      subst hevs
      exact ⟨rfl, rfl, e, List.mem_append.mpr (Or.inl hmem), heff⟩
    · rw [err_ret_ok] at Hrange
      obtain ⟨heff, rfl, rfl⟩ := Hrange
      exact ⟨rfl, rfl, ERANGE, List.mem_append.mpr (Or.inr (by simp)), heff⟩

/-- …AND EVERY ONE OF THE FOUR IS ADMITTED on the band: the `alt` is a
    genuine four-way choice, not a ranked list, and the completeness half
    is what lets a caller treat all four as live. -/
theorem getcwd_spec_band_ok (size : word) (H : size.toNat ≤ 1)
    (i : SyscallInput) (m : Model) (e : Int) (he : e ∈ getcwd_errnos ++ [ERANGE]) :
    getcwd_spec size i m (.ok (mkEffect (errno_ret e) [] []) m []) := by
  simp only [getcwd_spec, ite_eq_right (Nat.not_lt.mpr H), alt]
  rcases List.mem_append.mp he with he | he
  · left
    refine bind_ok _ _ i m e m [] (mkEffect (errno_ret e) [] []) m [] ?_ rfl
    exact (errno_from_ok _ i m e m []).mpr ⟨he, rfl, rfl⟩
  · right
    have heq : e = ERANGE := by simpa using he
    subst heq
    exact (err_ret_ok ERANGE i m (mkEffect (errno_ret ERANGE) [] []) m []).mpr
      ⟨rfl, rfl, rfl⟩

/-- The return words the spec can hand back, and no others: the three
    injectable errnos and -ERANGE.  -EINVAL is not among them — the kernel
    has no such arm — and that is what the next two checks spend. -/
theorem getcwd_spec_ret (size : word) (i : SyscallInput) (m : Model)
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : getcwd_spec size i m (.ok eff m' evs)) :
    m' = m ∧ evs = [] ∧
      eff.eff_ret ∈ getcwd_errnos.map errno_ret ++ [errno_ret ERANGE] := by
  obtain ⟨hmm, hevs, e, he, heff⟩ := getcwd_spec_admitted size i m H
  refine ⟨hmm, hevs, ?_⟩
  subst heff
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨e, he, rfl⟩))
  · have heq : e = ERANGE := by simpa using he
    subst heq
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-! ### The size-0 / size-1 band -/

/-- `getcwd(NULL, 0)` is -ERANGE, and it is ADMITTED: the deterministic
    arm the kernel reaches after the whole path has been assembled and
    found not to fit. -/
example : getcwd_spec 0 demoInput demoModel
    (.ok (errEffect ERANGE) demoModel []) := by
  refine alt_r _ _ _ _ _ ?_
  simp [err_ret, ret_only, errEffect, pure]

/-- `getcwd(buf, 1)` is -ERANGE too: one byte cannot hold even the
    terminating NUL — the kernel builds into a KERNEL page first and then
    fails the `len > size` test with `len >= 2`. -/
example : getcwd_spec 1 demoInput demoModel
    (.ok (errEffect ERANGE) demoModel []) := by
  refine alt_r _ _ _ _ _ ?_
  simp [err_ret, ret_only, errEffect, pure]

/-- -ENOMEM IS ADMISSIBLE FOR THE SAME CALL: `__getname()` runs before
    anything else and its allocation can fail.  The witness is the first
    element of `getcwd_errnos`; `bind_ok`/`choose_ok` are the
    introduction lemmas that build it, since `simp` cannot invent a
    witness for the `choose`. -/
example : getcwd_spec 0 demoInput demoModel
    (.ok (errEffect ENOMEM) demoModel []) := by
  refine alt_l _ _ _ _ _ ?_
  exact bind_ok _ _ demoInput demoModel ENOMEM demoModel [] (errEffect ENOMEM)
    demoModel [] (choose_ok _ ENOMEM demoInput demoModel (by decide)) rfl

/-- -ENOENT IS ADMISSIBLE as well: the caller's working directory may have
    been rmdir'd by another process since it was entered. -/
example : getcwd_spec 1 demoInput demoModel
    (.ok (errEffect ENOENT) demoModel []) := by
  refine alt_l _ _ _ _ _ ?_
  exact bind_ok _ _ demoInput demoModel ENOENT demoModel [] (errEffect ENOENT)
    demoModel [] (choose_ok _ ENOENT demoInput demoModel (by decide)) rfl

/-- …and so is -ENAMETOOLONG, the third injectable answer. -/
example : getcwd_spec 0 demoInput demoModel
    (.ok (errEffect ENAMETOOLONG) demoModel []) := by
  refine alt_l _ _ _ _ _ ?_
  exact bind_ok _ _ demoInput demoModel ENAMETOOLONG demoModel []
    (errEffect ENAMETOOLONG) demoModel []
    (choose_ok _ ENAMETOOLONG demoInput demoModel (by decide)) rfl

/-- The completeness half is usable directly: `size 1` admits -ENOMEM
    through `getcwd_spec_band_ok`, with the membership supplied rather
    than a witness hand-built. -/
example : getcwd_spec 1 demoInput demoModel
    (.ok (errEffect ENOMEM) demoModel []) :=
  getcwd_spec_band_ok 1 (by decide) demoInput demoModel ENOMEM
    (List.mem_append.mpr (Or.inl (by simp [getcwd_errnos])))

/-- NOTHING IS WRITTEN ON ANY ADMITTED ARM: the five ledgers are empty and
    the model is left alone, which is the `buf`-is-not-an-argument claim
    in the form a caller can use. -/
theorem getcwd_spec_admitted_inert (size : word) (i : SyscallInput) (m : Model)
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : getcwd_spec size i m (.ok eff m' evs)) :
    m' = m ∧ evs = [] ∧ eff.eff_writes = [] ∧ eff.eff_zeros = [] ∧
      eff.eff_unmaps = [] ∧ eff.eff_copies = [] ∧ eff.eff_copyins = [] := by
  obtain ⟨hmm, hevs, e, -, heff⟩ := getcwd_spec_admitted size i m H
  subst heff
  exact ⟨hmm, hevs, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The POSIX -EINVAL is not an arm -/

/-- -EINVAL is not one of the four return words: the four are the three
    injectable errnos and -ERANGE, and none of them is 22. -/
example : errno_ret EINVAL ∉ getcwd_errnos.map errno_ret ++ [errno_ret ERANGE] := by
  decide

/-- THE POSIX -EINVAL FOR A ZERO SIZE IS NOT MODELLED, and this is the
    check that says so: the kernel body has no -EINVAL arm at all, so
    `getcwd(NULL, 0)` never returns it here.  The `EINVAL` a glibc caller
    sees for a zero size is decided in
    `sysdeps/unix/sysv/linux/getcwd.c` before the syscall is issued, so a
    trace that carries it into the kernel is one Linux does not produce. -/
example : ¬ getcwd_spec 0 demoInput demoModel
    (.ok (errEffect EINVAL) demoModel []) := by
  intro H
  have hmem := (getcwd_spec_ret 0 demoInput demoModel H).2.2
  exact absurd (by simpa [errEffect] using hmem) (by decide)

/-- …and the same for a one-byte buffer: the -EINVAL story is not a
    small-size arm at either end of the band. -/
example : ¬ getcwd_spec 1 demoInput demoModel
    (.ok (errEffect EINVAL) demoModel []) := by
  intro H
  have hmem := (getcwd_spec_ret 1 demoInput demoModel H).2.2
  exact absurd (by simpa [errEffect] using hmem) (by decide)

/-- …nor is it an arm above the band, where the call is declined rather
    than answered. -/
example : ¬ getcwd_spec 2 demoInput demoModel
    (.ok (errEffect EINVAL) demoModel []) := by
  intro H
  have h := (getcwd_spec_big 2 demoInput demoModel (by decide) _).mp H
  exact absurd h (by simp)

/-! ### `buf` is not an argument

    The header's ORDER paragraph: the kernel's sequence reaches ERANGE
    only after the whole path was built into a KERNEL page, and there is
    no `access_ok` and no probe of `buf` anywhere earlier.  So the answer
    must not change when every address maps — a spec that consulted
    `in_wmem` would answer -EFAULT here, and `getcwd(NULL, 0)` really is
    -ERANGE. -/

/-- The same input with a fully mapped, fully writable user address
    space.  The spec does not read it. -/
private def demoInputMapped : SyscallInput :=
  { in_sysno := 17, in_args := [0, 0], in_mem := fun _ => some 0,
    in_wmem := fun _ => some 0 }

/-- A mapped `buf` does not change the answer: still -ERANGE. -/
example : getcwd_spec 0 demoInputMapped demoModel
    (.ok (errEffect ERANGE) demoModel []) := by
  refine alt_r _ _ _ _ _ ?_
  simp [err_ret, ret_only, errEffect, pure]

/-- …and it certainly does not produce -EFAULT, the answer a spec that
    probed `buf` would have given. -/
example : ¬ getcwd_spec 0 demoInputMapped demoModel
    (.ok (errEffect EFAULT) demoModel []) := by
  intro H
  have hmem := (getcwd_spec_ret 0 demoInputMapped demoModel H).2.2
  exact absurd (by simpa [errEffect] using hmem) (by decide)

/-! ### The decline: `size ≥ 2` is `unmodeled`, never a fabricated path -/

/-- A two-byte buffer is past the band — the working directory WOULD
    decide the answer — so the call is declined, fail closed. -/
example : getcwd_spec 2 demoInput demoModel .unmodeled := by
  simp [getcwd_spec, unmodeled]

/-- …and so is a full PATH_MAX buffer: the size being large does not let
    the model invent the string. -/
example : getcwd_spec 4096 demoInput demoModel .unmodeled := by
  simp [getcwd_spec, unmodeled]

/-- A register at `2^64 - 1` reads as an enormous UNSIGNED size rather
    than as -1 (`bv_unsigned`, here `toNat`), so it is declined too. -/
example : getcwd_spec (BitVec.ofInt 64 (-1)) demoInput demoModel .unmodeled := by
  simp [getcwd_spec, unmodeled]

/-- The decline is TOTAL above the band: no `ok` outcome at all, which is
    what "fail closed" means for the success and -EFAULT arms both. -/
example : ¬ ∃ eff m' evs, getcwd_spec 2 demoInput demoModel (.ok eff m' evs) := by
  rintro ⟨eff, m', evs, H⟩
  have h := (getcwd_spec_big 2 demoInput demoModel (by decide) _).mp H
  exact absurd h (by simp)

/-! ### The success arm this spec deliberately does not have

    A check that `getcwd_spec` writes "." and its NUL does not exist, and
    cannot: on every admitted arm nothing is written
    (`getcwd_spec_admitted_inert`), and above the band the call is
    declined.  The "." answer is precisely the part that needs a working
    directory.  What IS pinned is the weaker statement the model owns: no
    admitted effect carries a single written byte, so no caller can
    observe a path from this spec. -/

/-- Not one admitted arm writes: the write ledger is empty for two of the
    four answers, and the theorem above covers all four. -/
example : (errEffect ERANGE).eff_writes = [] := rfl

example : (errEffect ENAMETOOLONG).eff_writes = [] := rfl

/-- …and the effect is exactly `ret_only`-shaped: a bare return, five
    empty ledgers, model untouched, no events. -/
example : errEffect ERANGE = mkEffect (errno_ret ERANGE) [] [] := rfl

end LinuxSem.LinuxProcessSem.Sys.Fs.DPath

