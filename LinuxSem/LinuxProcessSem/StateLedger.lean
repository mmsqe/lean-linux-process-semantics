/-
  * LinuxProcessSem.StateLedger — ledger core, accessors, setters

  In three groups:

  - `alloc_top` and its three bounds, `mkVmMaps`, `alloc_top_mkVmMaps`,
  `live_bytes`, `vm_live_bytes`;
  - `creds_privileged`;
  - the 25 `m_*` accessors, `overflow_id`, `default_nofile`, `mkModel`,
  `statpins_restrict`, `statpin_lookup`, the 24 `with_*` setters,
  `killed_is_halted` and `m_killed_of_m_halted_none`.

  `event` is already in `State.lean` and is not repeated here.

  TRUST BOUNDARY: this file is part of the trusted specification.

  ACCESSORS AND SETTERS ARE `def`, NOT `abbrev`.  Every `m_*` and
  `with_*` has to stay opaque to `simp`: unfolding one also unfolds a bare
  `m_fs model`, "which later steps match on literally, and then cannot
  find".  Lean gives that with `def` — `simp` treats a `def` body as
  opaque and only `rfl` (or an explicit `simp [m_fds]`) unfolds it —
  whereas `abbrev` would unfold everywhere and break those downstream
  match sites.  No `simp` attribute is put on any accessor or setter
  here: the accessor/setter IDENTITY lemmas that would carry one live in
  `StateMatrix`, and every lemma that IS in this file (`alloc_top_room`,
  `alloc_top_lt`, `alloc_top_page_lt`, `alloc_top_mkVmMaps`,
  `stack_max_size_val`, `killed_is_halted`,
  `m_killed_of_m_halted_none`) carries no such attribute either.

  `bv_unsigned`.  There is no `bv_unsigned` in this tree, so `alloc_top`
  and `live_bytes` use `.toNat` — the same function on the same carrier,
  `(w.toNat: Int)` for every `w: word` — and the three `alloc_top_*`
  bounds are proved directly from `BitVec.isLt` rather than from a range
  lemma about `bv_unsigned`.

  `alloc_top_bounds`.  Two `omega`-fodder facts — `alloc_top_room h` and
  `stack_max_size_val`, for every ledger a hypothesis mentions — are
  already lemmas here, so a site that needs them names them
  (`alloc_top_room h`, `have`-bound) or derives the bound with `omega`.  No
  bundled declaration of the pair is offered: it would introduce nothing
  and would hide which ledger the bound is about.

  DEPENDENCY.  `mkModel` and `with_accepted` name `net_silent` and
  `nq_rest`, which live in `StateNet.lean`.  This module imports that one for exactly those two
  names.  They are NOT redeclared here: a duplicate declaration in the
  same namespace would break the root build, so the import is the
  dependency and the copies stay only in `StateNet.lean`.
-/
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.StateNet

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/- =========================================================================
  The allocation top
   ========================================================================= -/

/-- **ALLOCATION TOP**: no allocator grant (anonymous mmap, brk grow, a
    moved or grown mremap) may reach at or above this address, so every
    grant is disjoint from the dynamic stack `sp - stack_max_size, sp`
    and from the argv/envp/auxv block above `sp` — for the `sp` THIS run
    was started with.

    A bound rather than a reservation entry, on purpose: `region_free`
    over a list holding a symbolic `sp`-based interval turns every
    concrete `grant_ok ... = true` in the examples into an open `bv`
    term, while one `Int` inequality keeps `sp` a single `omega` atom.
    The price is that a hinted grant INTO the stack band — which Linux
    honours when the hint is free — is refused here rather than
    declined.

    Computed in `Int` from a `word`, so it is below 2^64 for every ledger
    (`alloc_top_lt`) with no wrap argument: that is what lets a proof
    conclude from `a + n <= alloc_top h` that `a + n` is a real address
    and never an encoded errno.

    `stack_max_size` stays a constant.  `Sys.lean`'s `prlimit64` note
    argues why `RLIMIT_STACK` is not modelled; until it is, 8 MiB is the
    only stack size the model knows. -/
def alloc_top (h : VmMaps) : Int :=
  ((h.vm_init_sp).toNat : Int) - stack_max_size

/-- The whole stack fits above the top, so a grant that ends at or
    below it ends a stack's width short of 2^64 — room enough that its
    address can never be read as an encoded errno. -/
theorem alloc_top_room (h : VmMaps) : alloc_top h + stack_max_size < two_pow_64 := by
  have h1 : ((h.vm_init_sp).toNat : Int) < two_pow_64 := by
    have hlt := (h.vm_init_sp).isLt
    have h2 : ((h.vm_init_sp).toNat : Int) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast hlt
    simpa [two_pow_64] using h2
  unfold alloc_top
  omega

theorem stack_max_size_val : stack_max_size = 8388608 := by decide

theorem alloc_top_lt (h : VmMaps) : alloc_top h < two_pow_64 := by
  have hroom := alloc_top_room h
  have hs : stack_max_size = 8388608 := stack_max_size_val
  omega

/-- One page above the top is still an address: the brk gate tests the
    page above the installed ones (`Sys/Mm/Mmap.brk_grow_ok`), and this
    is the bound that keeps that range from wrapping. -/
theorem alloc_top_page_lt (h : VmMaps) : alloc_top h + page_size < two_pow_64 := by
  have hroom := alloc_top_room h
  have hp : page_size = 4096 := by decide
  have hs : stack_max_size = 8388608 := stack_max_size_val
  omega

/-- Compatibility constructor for ledgers containing only rw memory.
    Existing examples and allocator simulations need not mention the
    empty protection ledger, nor the placement base (seeded 0, which
    means "no base recorded" and which nothing in the spec reads; see
    the `vm_mmap_base` note above).  The stack pointer is seeded at the
    BOTTOM of the SP window, so a hand-built ledger's `alloc_top` is the
    smallest any admissible run has: what such a ledger admits, every
    run admits. -/
def mkVmMaps (reserved maps : List (word × word))
    (start_brk brk : word) (limit : Int) : VmMaps :=
  VmMaps.mkVmMapsFull reserved maps [] start_brk brk limit
    (BitVec.ofInt 64 0) (BitVec.ofInt 64 sp_window_lo)

theorem alloc_top_mkVmMaps (reserved maps : List (word × word))
    (start_brk brk : word) (limit : Int) :
    alloc_top (mkVmMaps reserved maps start_brk brk limit) = 0x7fff7f800000 := by
  have h : (BitVec.ofInt 64 sp_window_lo).toNat = 0x7fff80000000 := by decide
  have hs : stack_max_size = 8388608 := stack_max_size_val
  simp only [alloc_top, mkVmMaps, h, hs]
  omega

/-- Bytes currently granted by a ledger: the sum of its interval sizes.

    The `vm_maps` intervals are pairwise disjoint AT PAGE GRANULARITY —
  no page-aligned address is owned by two entries.
    `Checks.VmMapsDisjoint.check_syscall_preserves_vm_wf` (in
  `Checks/VmMapsDisjoint/Chain.lean`) proves that every modeled syscall
  preserves that disjointness from `init_model` on:
    `CheckOk i eff m m' evs → vm_wf (m_vmmaps m) → vm_wf (m_vmmaps m')`.
    It is **UNCONDITIONAL** — an unmodelled sysno makes the hypothesis
    impossible, so there is no coverage premise — and it rests on the
    90-arm table `checked_table_preserves_vm`, which applies one
    `arm_*_preserves_vm` per arm in table order, so no arm can be silently
    dropped.  The four mm writers (mmap/munmap/mremap/mprotect, the only
    arms whose grant can overlap a live mapping) are the interesting ones
    and are proved in `Chain/Writers.lean`.

    NOTE ON CITATION, not on truth: this file **cannot import** it —
    `StateVm` imports `StateLedger`, and the chain's `Core` imports
    `StateVm`, so the edge would be a cycle.  The sentence above is
    therefore a PROSE citation of a result that lives in a module above
    this one.  If the budget argument below is to *use* it rather than
    cite it, the use site has to live above `Checks/` (e.g.
    `Checks/BudgetPremise`).

    The intervals are NOT pairwise disjoint byte for byte, so this sum is
    NEITHER AN UPPER NOR A LOWER BOUND on the granted-and-not-freed bytes
    — two sub-page brk gaps move it in OPPOSITE directions — both for
    `vm_live_bytes` here and downstream in `vm_backed_bytes` and
    `vm_backing_used`, which measure this same sum over ledgers derived
    from `vm_maps` by subtraction.

    OVER-COUNT, from a brk GROW that does not cross a page boundary.
    `Sys/Mm/Mmap.brk_grants` records the logical range `old, r` while
    `Sys/Mm/Mmap.brk_grow_ok` tests the page-rounded one (plus the page
    above it) and tests nothing when that range is EMPTY, as it is for
    such a grow, so the grant enters with no address-space test
    and entries can overlap — the same bytes counted twice.  That one is
    FAITHFUL rather than a slip: `SYSCALL_DEFINE1(brk)` takes its
    `oldbrk == newbrk` early exit before consulting any VMA, so Linux too
    lets the break walk over bytes another mapping owns (reachable by
    unmapping the brk VMA and mapping over it).
    `Checks/VmMapsDisjoint` carries a checked six-syscall execution that
  reaches exactly that state: `wit_step1` … `wit_step5` then
  `wit_overlap_step` in `Checks/VmMapsDisjoint/Core.lean` reach a ledger
  whose entries overlap (`wit_overlap_holds`), so the state this
  paragraph describes is exhibited here, not merely described.
    Over-counting can only bring the forced
    out-of-memory point EARLIER, which is the safe direction.

    UNDER-COUNT, from a brk SHRINK that does not cross a page boundary,
    and this one is a KNOWN INCONSISTENCY rather than faithful modelling.
    `Sys/Mm/Mmap.brk_maps_next`'s shrink arm subtracts the RAW range
    `r, b` from `vm_maps`, while `Sys/Mm/Mmap.brk_unmaps` reports the
    PAGE-ROUNDED one, which is empty for such a shrink.  So the effect
    says nothing was freed, Linux's `oldbrk == newbrk` exit frees no VMA
    at all, and the ledger drops the bytes anyway:
  `Checks.VmMapsDisjoint.wit_step6` (`Checks/VmMapsDisjoint/Core.lean`)
  shrinks the break by 10 bytes inside one page and the ledger goes from
  `(65536, 4096)` to
    `(65536, 1990); (67536, 2096)` — 4096 bytes to 4086, ten granted,
    unfreed, still-mapped bytes gone from the sum.  Under-counting moves
    the forced out-of-memory point LATER, which is the UNSAFE direction,
    and no gate compensates for it.  The two are not reconciled.

    `munmap`, a shrinking `mremap`, and a `brk` shrink return their bytes
    to the budget by shrinking the ledger.  Placement plays no part — the
    budget meters BYTES, not addresses — which is what makes the forced
    out-of-memory point deterministic. -/
def live_bytes : List (word × word) → Int
  | [] => 0
  | (_, sz) :: r => (sz.toNat : Int) + live_bytes r

def vm_live_bytes (h : VmMaps) : Int := live_bytes h.vm_maps

/- =========================================================================
  Credentials
   ========================================================================= -/

/-- **WHAT "PRIVILEGED" MEANS HERE**, and what it assumes.

    The kernel never asks whether a caller is root.  Each credential
    setter asks `ns_capable_setid(old->user_ns, CAP_SETUID)` (or
    CAP_SETGID), which reads one bit out of `cred->cap_effective`
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/capability.c,
    `ns_capable_setid`; security/commoncap.c, `cap_capable_helper`, the
    inline the tracing wrapper `cap_capable` calls — v6.14 moved the
    loop out of `cap_capable` to add a tracepoint, and the answer it
    computes for the init user namespace,
    `cap_raised(cred->cap_effective, cap) ? 0 : -EPERM`, is unchanged
    from v6.10 through v6.18).  The model carries no capability sets,
    so it answers the question with the effective uid instead.

    That is exact, not a guess, PROVIDED: the init user namespace; the
    executed binary carries no file capabilities; no ambient
    capabilities; default securebits — none of SECURE_NOROOT,
    SECURE_KEEP_CAPS, SECURE_NO_SETUID_FIXUP; and an UNNARROWED
    capability bounding set.  The last is easy to miss and is not
    implied by the others: `handle_privileged_root` grants legacy root
    `new->cap_permitted = cap_combine(old->cap_bset, old->cap_inheritable)`
    (security/commoncap.c), so an ancestor that ran
    `prctl(PR_CAPBSET_DROP, CAP_SETUID)` leaves every later exec with
    euid 0 and no CAP_SETUID at all.  Under those,
    `cap_emulate_setxuid` (security/commoncap.c, byte-identical at all
    six tags in the window) runs on every `set*uid` and maintains

      CAP_SETUID in cap_effective  <->  euid = 0

    in both directions: it clears `cap_effective` on every euid 0 ->
    non-0 transition, restores `cap_effective = cap_permitted` on
    non-0 -> 0, and clears `cap_permitted` outright once ALL of uid,
    euid and suid have left 0.  The last case is absorbing rather than a
    counterexample: from it, `__sys_setuid`'s unprivileged branch can
    reach only the (non-zero) real and saved uids and `__sys_setresuid`'s
    only the three (non-zero) old ids, so euid = 0 is unreachable and
    both sides of the biconditional stay false forever.  `setgid` and
    `setresgid` never touch capabilities at all.

    Each excluded condition breaks the biconditional in a DIFFERENT
    direction, which is why they are assumptions and not slack: file
    capabilities, ambient capabilities and a non-init user namespace give
    a non-root process the capability (the model would then refuse a call
    the kernel allows); SECURE_NOROOT and a narrowed bounding set
    withhold it from root (the model would allow a call the kernel
    refuses).  A run in any of those environments is outside this model.

    `init_model` pins the process's starting point to an ordinary exec —
    it derives the effective and saved ids from the real ones rather than
    taking them as input — which is the same world. -/
def creds_privileged (c : Creds) : Bool :=
  bv_eqb c.cr_euid (BitVec.ofInt 64 0)

/- =========================================================================
  The accessors
   ========================================================================= -/

/-- The accessors the rest of the development uses; they hide the
    nesting.

  They are `def`s, not `abbrev`s, so that `simp` never unfolds one by
  accident (see the file header). -/
def m_fds (m : Model) : List (word × FdEntry) := m.m_fd.fdst_table

def m_pipes (m : Model) : List (word × PipeBuf) := m.m_fd.fdst_pipes

def m_vmmaps (m : Model) : VmMaps := m.m_vm.vmst_maps

def m_vm_lazy (m : Model) : List (word × word) := m.m_vm.vmst_lazy

def m_vm_materialized (m : Model) : List word :=
  m.m_vm.vmst_materialized

def m_stdin (m : Model) : InputStream := m.m_io.iost_stdin

def m_urandom (m : Model) : InputStream := m.m_io.iost_urandom

def m_net (m : Model) : NetQueue := m.m_io.iost_net

def m_conn_ix (m : Model) : word := m.m_io.iost_conn_ix

def m_fs (m : Model) : Fs.Fs := m.m_fsys.fsst_image

def m_halted (m : Model) : Option word := m.m_proc.procst_halted

def m_tid (m : Model) : Option word := m.m_proc.procst_tid

def m_setsid_succeeded (m : Model) : Bool :=
  m.m_proc.procst_setsid_succeeded

def m_has_children (m : Model) : Bool := m.m_proc.procst_children

def m_sigaltstack_installed (m : Model) : Bool :=
  m.m_proc.procst_sigaltstack_installed

def m_sigmask (m : Model) : word := m.m_proc.procst_sigmask

/-- The signal that killed the process, or `none` if it exited or is
    still running.  READ THROUGH `procst_halted` on purpose: the payload
    is the halt's, and the flag only says how to read it.  That is what
    makes `m_killed_of_m_halted_none` hold with no side condition. -/
def m_killed (m : Model) : Option word :=
  if m.m_proc.procst_killed then m.m_proc.procst_halted else none

def m_sigabrt_pending (m : Model) : Bool :=
  m.m_proc.procst_sigabrt_pending

def m_abort_terminal (m : Model) : Bool :=
  m.m_proc.procst_abort_terminal

def m_utsname (m : Model) : Option (List byte) :=
  m.m_proc.procst_utsname

def m_statpins (m : Model) : List (Fs.path × List byte) :=
  m.m_proc.procst_statpins

def m_rlimit_core (m : Model) : Option (List byte) := m.m_lim.limst_core

def m_nofile (m : Model) : word := m.m_lim.limst_nofile

def m_clock (m : Model) : word := m.m_time.timest_clock

def m_creds (m : Model) : Creds := m.m_proc.procst_creds

/- =========================================================================
  Constants of a model built without a `ProcInput`
   ========================================================================= -/

/-- The id the kernel itself answers with when it has no id to answer:
    `DEFAULT_OVERFLOWUID` / `DEFAULT_OVERFLOWGID`, both 65534
    (include/linux/highuid.h), which `from_kuid_munged` substitutes for
    an id that does not map into the caller's namespace
    (kernel/user_namespace.c).  It is what `mkModel` gives a model built
    WITHOUT a `ProcInput`, below.

    Not zero, and that is the point.  Zero would make every such model a
    ROOT process, and `creds_privileged` reads the effective uid: a
    worked example that meant to say nothing about privilege would have
    been saying the most permissive thing there is.  A model that needs
    root says so, with `with_creds`. -/
def overflow_id : word := BitVec.ofInt 64 65534

/-- The soft RLIMIT_NOFILE a model built WITHOUT a `ProcInput` gets:
    `INR_OPEN_CUR`, the value `INIT_RLIMITS` gives the init task
    (include/asm-generic/resource.h; include/uapi/linux/fs.h,
    `#define INR_OPEN_CUR 1024`, Linux v6.18.46, commit 1f99e9ab748f).
    It is what a process is launched with on a system where nobody
    changed the limit, so a fixture that means to say nothing about the
    descriptor limit says the ordinary thing.

    Not a permissiveness choice the way `overflow_id` is: 0 would make
    every `dup3` in such a fixture -EBADF and RLIM_INFINITY is not a
    value `do_prlimit` lets NOFILE hold at all (kernel/sys.c refuses a
    hard limit above `sysctl_nr_open`).  A run built from a `ProcInput`
    never sees this: `init_model` installs `in_nofile` over it. -/
def default_nofile : word := BitVec.ofInt 64 1024

/-- `mkModel` keeps the flat constructor's argument order, so every site
    that builds a model is unchanged.  The random device's stream starts
    EMPTY here (`IEof`) for the reason the accept queue starts silent:
    it is an input of the run, and the one place that installs one is
    `init_model`, through `with_urandom`. -/
def mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word)
    (tid : Option word) (rlim : Option (List byte)) : Model :=
  Model.mkModelOf
    { fdst_table := fds, fdst_pipes := [] }
    { vmst_maps := vm, vmst_lazy := [], vmst_materialized := [] }
    { iost_stdin := stdin, iost_urandom := IEof, iost_net := net_silent,
      iost_conn_ix := BitVec.ofInt 64 0 }
    { fsst_image := fs }
    { procst_halted := halted, procst_tid := tid
      procst_creds :=
        { cr_uid := overflow_id, cr_euid := overflow_id, cr_suid := overflow_id
          cr_gid := overflow_id, cr_egid := overflow_id, cr_sgid := overflow_id
          cr_groups := [] }
      procst_setsid_succeeded := false, procst_sigmask := BitVec.ofInt 64 0
      procst_children := false, procst_utsname := none
      procst_sigaltstack_installed := false, procst_killed := false
      procst_sigabrt_pending := false, procst_abort_terminal := false
      procst_statpins := [] }
    { limst_core := rlim, limst_nofile := default_nofile }
    { timest_clock := BitVec.ofInt 64 0 }

/- =========================================================================
  The setters
   ========================================================================= -/

/-- Field-update helpers.  Each one rebuilds only its own subsystem and
    carries the other five across, so a new field inside a subsystem
    touches that subsystem's setters and no others.

  Lean's `with`-record update syntax is definitionally the same thing as
  restating all seven `mkModelOf` fields (every carried field is a
  literal projection of `m`), and it removes a whole class of bug — a
  new setter that rebuilds a subsystem without carrying a field breaks
  the composition without breaking either side's proofs. -/
def with_fds (fds : List (word × FdEntry)) (m : Model) : Model :=
  { m with m_fd := { m.m_fd with fdst_table := fds } }

def with_pipes (ps : List (word × PipeBuf)) (m : Model) : Model :=
  { m with m_fd := { m.m_fd with fdst_pipes := ps } }

def with_vmmaps (h : VmMaps) (m : Model) : Model :=
  { m with m_vm := { m.m_vm with vmst_maps := h } }

def with_vm_backing (lazy : List (word × word))
    (materialized : List word) (m : Model) : Model :=
  { m with m_vm := { m.m_vm with vmst_lazy := lazy,
                                 vmst_materialized := materialized } }

def with_stdin (s : InputStream) (m : Model) : Model :=
  { m with m_io := { m.m_io with iost_stdin := s } }

/-- The random device's remaining stream.  `init_model` installs the
    declared one; every later call is a read on `FdUrandom` advancing
    past the bytes it delivered (`Fs.ReadWrite.read_urandom`). -/
def with_urandom (s : InputStream) (m : Model) : Model :=
  { m with m_io := { m.m_io with iost_urandom := s } }

/-- Seed the accept queue.  Its only caller is `init_model`, which is
    the point: the queue is an INPUT of the run, so the one place that
    may install one is the one that turns a `ProcInput` into a model.
    Every later change to it goes through `with_accepted`, which cannot
    install a queue, only advance past its head. -/
def with_net (q : NetQueue) (m : Model) : Model :=
  { m with m_io := { m.m_io with iost_net := q } }

/-- Install a new file-system image, DROPPING THE STAT PIN of every path
    the new image does not hold.

    THE FILTER IS NOT BOOKKEEPING; IT IS THE PIN'S CORRECTNESS
    CONDITION.  `procst_statpins` holds a path's inode identity for the
    life of the file, and `unlinkat` (35) — the one modeled syscall
    that takes a key OUT of the map — destroys it.  A pin that survived
    the removal would be held against the NEXT file created at that
    name, which Linux gives a different inode, so
    `Fs.Stat.fstat_file_spec` would reject the conforming trace
    `create f; fstat; unlink f; create f; fstat`.  Every other writer of
    this field passes a map that still holds the path it is about —
    `Open.create_wronly`'s O_TRUNC keeps the key, and so do
    `ReadWrite.write_spec` and `Open.ftruncate_spec` — so the filter is
    inert for all of them, which is what makes routing the invalidation
    through this one setter equivalent to putting it in `unlinkat` and
    cheaper than remembering to.

    A CREATE OVER AN EXISTING FILE KEEPS THE PIN, and should: O_TRUNC
    resizes an inode rather than replacing it, and `st_size` is not a
    member the pin holds fixed anyway. -/
def statpins_restrict (fs : Fs.Fs) (ps : List (Fs.path × List byte)) :
    List (Fs.path × List byte) :=
  ps.filter (fun e => match Fs.fs_lookup fs e.1 with
                      | some _ => true
                      | none => false)

def with_fs (fs : Fs.Fs) (m : Model) : Model :=
  { m with
    m_fsys := { m.m_fsys with fsst_image := fs },
    m_proc := { m.m_proc with
                  procst_statpins := statpins_restrict fs m.m_proc.procst_statpins } }

/-- Halt the process by an EXIT, which is the other half of what the
    kill flag distinguishes: this clears it, so a model this produced has
    `m_killed` `none` whatever it had before.  Nothing can reach it with
    the flag already set — every rule that consumes a syscall outcome
    requires the process to be running — and clearing rather than
    carrying is what makes `m_killed_with_halted` the `none` the two
    terminal rules need to stay disjoint. -/
def with_halted (code : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_halted := some code,
                                      procst_killed := false } }

def with_tid (tid : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_tid := some tid } }

def with_rlimit_core (bs : List byte) (m : Model) : Model :=
  { m with m_lim := { m.m_lim with limst_core := some bs } }

/-- Record the UTS name the environment revealed.
    `Kernel.Sys.uname_spec` is the only caller and it calls this only on
    the branch where `m_utsname` was `none`, so the pin is written once
    and never overwritten: `uname` (160) is a pure read, and the two
    syscalls that WRITE a utsname field — `sethostname` (161) and
    `setdomainname` (162) — have no arm in
    `Sys.SyscallTable.spec_table`.  That is what makes the repeat check
    in `Checks.Sys.Kernel.Sys`'s `check_uname_copy` an equality rather
    than a relation, and adding either syscall means giving this a
    second writer in the same commit. -/
def with_utsname (bs : List byte) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_utsname := some bs } }

/-- Look a file's stat pin up by path.  `none` means no `fstat` has
    delivered a `struct stat` for that file yet, which is the branch
    that CREATES one.  Linear over an association list, like
    `Fs.fs_lookup` and `fd_lookup` beside it. -/
def statpin_lookup : List (Fs.path × List byte) → Fs.path → Option (List byte)
  | [], _ => none
  | (q, bs) :: rest, p =>
      if Fs.path_eqb q p then some bs else statpin_lookup rest p

/-- Record the `struct stat` a file was first seen with.
    `Fs.Stat.fstat_spec` is the only caller and it calls this only on
    the branch where `statpin_lookup` was `none`, so a path's pin is
    written once and never overwritten — which is what lets
    `Checks.Sys.Fs.Stat`'s repeat check be a comparison against the
    stored bytes rather than a relation between two calls.  The entry is
    CONSED rather than merged into a sorted list on purpose: unlike
    `Fs.fs_set`, nothing observes this field's representation, so it
    owes no canonical form.

    A second writer would have to argue why the pin may move.  There is
    no such argument for the members `Uapi.stat_stable_eqb` compares —
    no `chmod`, `chown` or `link` arm exists in
    `Sys.SyscallTable.spec_table` — so adding one means revisiting that
    predicate in the same commit, not adding a call here. -/
def with_statpin (p : Fs.path) (bs : List byte) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with
                         procst_statpins := (p, bs) :: m.m_proc.procst_statpins } }

/-- Seed the task's abort-path declaration.  Its only caller is
    `init_model`, for the reason `with_net` and `with_nofile` give: the
    declaration is a parameter of the RUN, so the one place that may
    install it is the one that turns a `ProcInput` into a model.  Unlike
    those two it has no reader anywhere in the model's own state
    transitions either — `Kernel.Signal.tkill_spec` reads it and nothing
    writes it after this — so the field is constant along every run, and
    that is what lets `Run.valid_input` pin a whole statement's stance by
    pinning one field of the input. -/
def with_abort_terminal (b : Bool) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_abort_terminal := b } }

/-- Seed the soft descriptor limit.  Its only caller is `init_model`, for
    the reason `with_net` gives: the limit is an INPUT of the run, so the
    one place that may install one is the one that turns a `ProcInput`
    into a model.  Unlike `with_net`, which `with_accepted` later
    advances past, there is no second writer of any kind — see
    `limst_nofile` for why there can be none — which is also the
    difference between this and `with_rlimit_core`. -/
def with_nofile (n : word) (m : Model) : Model :=
  { m with m_lim := { m.m_lim with limst_nofile := n } }

def with_creds (c : Creds) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_creds := c } }

def with_setsid_succeeded (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_setsid_succeeded := true } }

/-- Record that the process now has something to reap.
    `Kernel.Fork.clone_resolve` calls this on its success branch, and only
    there — the errno alternative creates nothing and the shared-file
    decline never reaches a resolution.

    MONOTONE ONCE SET, and that is load-bearing rather than incidental:
    `Kernel.Exit.wait4_spec`'s -ECHILD gate reads this field at a LATER
    call than the one that sets it, so the two lemmas only compose while
    nothing clears it in between.  Every setter above either passes
    `m_proc m` through wholesale or carries `procst_children` explicitly,
    and `mkProcState` is constructed nowhere outside this file.  A new
    setter that rebuilds `ProcState` without carrying this field breaks
    the composition WITHOUT breaking either side's proofs: the gate would
    still be proved, the creating arm's setter would still be proved, and
    the model would answer -ECHILD for a caller that has a child.  Two
    true lemmas and still a hole.  If you add a `ProcState` construction
    site, carry this field. -/
def with_children (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_children := true } }

/-- Install a new blocked mask.  `Kernel.Signal.rt_sigprocmask_spec` is
    the only caller, and the only kernel path that reaches
    `__set_task_blocked` from a syscall this model answers: every other
    one — `rt_sigsuspend` (133), `rt_sigtimedwait` (137),
    `epoll_pwait` (22), `io_pgetevents` (292), `io_uring_enter` (426),
    `ptrace` (117) and sigreturn (139) — is outside
    `Specs.modeled_sysnos`, and `pselect6` (72) and `ppoll` (73) reach
    their own mask arguments only through `Fs.Select`'s `PsSigReal` and
    `PpSigReal`, both of which are `unmodeled`.  THOSE TWO ARE THE
    FRAGILE HALF: each is an absence, so relaxing either means moving
    the mask here in the same commit, the way `set_user_sigmask` and
    `restore_saved_sigmask_unless` move it in fs/select.c. -/
def with_sigmask (s : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_sigmask := s } }

/-- Record that a `sigaltstack` has installed an alternate stack.
    `Kernel.Signal.sigaltstack_spec` is the only caller, and it calls
    this on exactly the branch where `do_sigaltstack` (kernel/signal.c)
    stores a NON-ZERO `t->sas_ss_size` — never on an errno branch, which
    leaves the record alone; never on the no-change fast path, which
    returns before the lock is taken; and never on the SS_DISABLE branch,
    which reaches the same three assignments but zeroes `ss_size` and
    `ss_sp` first and so leaves the record in the zero-size shape the
    spec can still answer from.

    MONOTONE ONCE SET, like `with_children`, and for a stronger reason:
    nothing in this model can shrink the recorded size back to zero — the
    one call that could, a later SS_DISABLE, is declined by the very bit
    this sets — so a setter that cleared it would be claiming the process
    is back in a state it cannot reach.  Every `ProcState` setter above
    carries the field across; a new one that does not would let the spec
    answer a `sigaltstack` from a zero-size record after an install moved
    it. -/
def with_sigaltstack_installed (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_sigaltstack_installed := true } }

/-- Record that SIGABRT has been sent and is BLOCKED, so it waits in
    `task->pending.signal` instead of ending the process
    (kernel/signal.c, `send_signal_locked` adds to the pending set and
    `recalc_sigpending` leaves a blocked signal there; Linux v6.18.46,
    commit 1f99e9ab748f).  `Kernel.Signal.tkill_spec` is the only caller.

    NOTHING CLEARS IT, and that is not an omission.  The kernel dequeues
    a pending signal when it delivers it (`dequeue_signal` from
    `get_signal`), but the only delivery this model has is the FATAL one:
    SIGABRT's disposition in a modeled run is SIG_DFL by construction —
    `Kernel.Signal.rt_sigaction_spec` declines every install for a signal
    outside SIGINT and SIGTERM — so the step that would clear the field
    is the step that ends the process, and no later state can read it.
    A second sendable signal, or a catchable SIGABRT, brings the clear
    with it. -/
def with_sigabrt_pending (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_sigabrt_pending := true } }

/-- End the process by a fatal signal.  It writes the signal number into
    `procst_halted`, because a killed process is over and every rule that
    asks whether the process is still running asks that field
    (`Run.sstep_instr` and its siblings).  Which of the two terminal
    rules fires is then decided by `procst_killed` alone —
    `Run.sstep_exit` declines a death by signal and `Run.sstep_killed`
    takes it — so the two cannot both apply.

    IT HAS TWO CALLERS, and which is which decides what guards them.
    `Kernel.Signal.send_sigabrt` is the SEND, and it sits behind the
    task's declaration.  `Kernel.Signal.sigmask_deliver_model` is the
    DELIVERY inside `rt_sigprocmask`, and it does NOT: it branches on
    `procst_sigabrt_pending`, because a signal already pending has to be
    taken by the mask install that uncovers it whatever the task
    declared.  A reader checking the declaration-off claim needs both
    rows — see `Run.decl_off_frame`, whose hypothesis carries the pending
    bit for exactly this reason, and
    `Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted`, which
    refutes the version that names only the declaration — **proved in this
    tree**, in `Checks/Cases/Kernel/Signal.lean`, so the refutation IS
    present here (`Run.lean` cites it too), and
    `Checks.Cases.Kernel.Signal.decl_off_frame_hypotheses_inhabited` sits
    beside it to show the hypothesis is not vacuous.  SIGABRT is the
    only argument either caller is ever given. -/
def with_killed (sig : word) (m : Model) : Model :=
  { m with m_proc := { m.m_proc with procst_halted := some sig,
                                      procst_killed := true } }

/-- The invariant the two fields are written under, stated where the
    setter is: a killed process is a halted process, and the two payloads
    agree.  `Run.sstep_killed` does not need it — it reads `m_killed` —
    but every rule that stops a running process does, and this is what
    says those rules stop a killed one. -/
theorem killed_is_halted (sig : word) (m : Model) :
    m_halted (with_killed sig m) = some sig ∧
      m_killed (with_killed sig m) = some sig := by
  constructor <;> rfl

/-- A PROCESS THAT IS STILL RUNNING HAS NOT BEEN KILLED, with no side
    condition and no premise about who wrote what.  This is what the flag
  representation buys, and every one-step inversion in `Common/`
  consumes it: a configuration whose `m_halted` is
    `none` cannot be the target of `Run.sstep_killed`, so an inversion
    that already ruled out `Run.sstep_exit` rules out both terminal
    rules together. -/
theorem m_killed_of_m_halted_none (m : Model) (h : m_halted m = none) :
    m_killed m = none := by
  by_cases hk : m.m_proc.procst_killed
  · simp only [m_halted] at h
    simpa [m_killed, hk] using h
  · simp [m_killed, hk]

def with_clock (t : word) (m : Model) : Model :=
  { m with m_time := { m.m_time with timest_clock := t } }

/-- Hand over the head of the accept queue: the fd table gains the
    accepted socket, the queue advances past the connection just taken,
    and the handed-over count goes up by one.  ONE helper rather than
    three, because the three moves are one event — `accept` is the only
    thing that changes any of them, and it always changes all three. -/
def with_accepted (fds : List (word × FdEntry)) (m : Model) : Model :=
  { m with
    m_fd := { m.m_fd with fdst_table := fds },
    m_io := { m.m_io with iost_net := nq_rest m.m_io.iost_net,
                          iost_conn_ix := m.m_io.iost_conn_ix + BitVec.ofInt 64 1 } }

/- =========================================================================
   Sanity checks

  `stack_max_size_val` (above) and `alloc_top_mkVmMaps` (above) are
  proved by `decide`; the examples below pin the accessors, the setters
  and `creds_privileged` against their defining equations.  They are
  anonymous on purpose: `StateMatrix` owns the NAMED `m_*_with_*`
  matrix and declares it.
   ========================================================================= -/

/-- After `with_fds` the fd table is the new list. -/
example (v : List (word × FdEntry)) (m : Model) : m_fds (with_fds v m) = v := rfl

/-- ... and the VM ledger is untouched. -/
example (v : List (word × FdEntry)) (m : Model) :
    m_vmmaps (with_fds v m) = m_vmmaps m := rfl

/-- `with_killed` writes the signal into BOTH `m_halted` and `m_killed`.

  The tempting variant `m_halted (with_killed v m) = m_halted m` is
  BACKWARDS: `with_killed` overwrites the halt payload, as it must,
  because a killed process is over, so that variant is FALSE for every
  `m` that was still running (`mkModel`, whose `procst_halted` is
  `none`, is a witness).  The `some v` asserted here is the true
  identity. -/
example (v : word) (m : Model) : m_halted (with_killed v m) = some v := rfl

example (v : word) (m : Model) : m_killed (with_killed v m) = some v := rfl

/-- An exit clears the kill flag, so `m_killed` is `none`. -/
example (v : word) (m : Model) : m_killed (with_halted v m) = none := rfl

/-- ... and the variant is refuted, not merely unproved: a running model
    (`mkModel`, whose `procst_halted` is `none`) is halted by
    `with_killed`. -/
example : ¬ ∀ (v : word) (m : Model), m_halted (with_killed v m) = m_halted m := by
  intro h
  have h1 := h 9 (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none)
  simp [m_halted, with_killed, mkModel] at h1

example (v : word) (m : Model) : m_nofile (with_nofile v m) = v := rfl

/-- `with_fs` rebuilds `ProcState`, so every field it CARRIES must still
  come through: this is the setter to watch (a dropped field breaks
  composition without breaking either side). -/
example (v : Fs.Fs) (m : Model) : m_halted (with_fs v m) = m_halted m := rfl

example (v : Fs.Fs) (m : Model) : m_creds (with_fs v m) = m_creds m := rfl

example (v : Fs.Fs) (m : Model) : m_has_children (with_fs v m) = m_has_children m := rfl

example (v : List (word × FdEntry)) (m : Model) : m_pipes (with_fds v m) = m_pipes m := rfl

/-- `with_fs` drops the pins the new image does not hold. -/
example (v : Fs.Fs) (m : Model) :
    m_statpins (with_fs v m) = statpins_restrict v (m_statpins m) := rfl

/-- `with_statpin` conses. -/
example (p : Fs.path) (bs : List byte) (m : Model) :
    m_statpins (with_statpin p bs m) = (p, bs) :: m_statpins m := rfl

/-- `creds_privileged` reads the EFFECTIVE uid, not the real one: a model
    built by `mkModel` (every id = `overflow_id` = 65534) is
    unprivileged, and `euid = 0` is what makes it privileged. -/
example : creds_privileged (Creds.mkCreds 0 0 0 0 0 0 []) = true := by decide

example : creds_privileged (Creds.mkCreds 1 0 0 0 0 0 []) = true := by decide

example : creds_privileged (Creds.mkCreds 0 1 0 0 0 0 []) = false := by decide

example : creds_privileged (Creds.mkCreds overflow_id overflow_id overflow_id
    overflow_id overflow_id overflow_id []) = false := by decide

/-- `mkVmMaps` seeds an empty protection ledger and a placement base of 0,
    and `alloc_top` reads the stack pointer, so a hand-built ledger's top
  is the lowest any run has.  `by decide` on the
    concrete ledger pins the definitional content of both. -/
example : (mkVmMaps [] [] 0 0 0).vm_noaccess = [] := rfl

example : (mkVmMaps [] [] 0 0 0).vm_mmap_base = 0 := by decide

example : live_bytes [(0, 4096), (8192, 4096)] = 8192 := by decide

example (m : Model) : vm_live_bytes (m_vmmaps (with_vmmaps (mkVmMaps [] [] 0 0 0) m)) = 0 :=
  rfl

end LinuxSem.LinuxProcessSem
