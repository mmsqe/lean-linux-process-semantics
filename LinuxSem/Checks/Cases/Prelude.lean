/-
  * LinuxProcessSem.Checks.Cases.Prelude — worked examples for the shared helpers

  Shared infrastructure for the worked examples below it: this one
  mirrors no kernel source, and holds nothing syscall-specific.

  `Checks.Examples` keeps what is not per-syscall and
  re-exports this module.  These are worked examples
  over the specs and checkers for the matching [Sys] module, read off
  without running a binary.

  Names.  The helpers keep the names the rest of the tree calls them by.
  Where the spelling differs: `Z` is `Int`, `bv n` is `BitVec n`,
  `Z_to_bv n z` is `BitVec.ofInt n z`, `bv_unsigned a` is
  `(a.toNat : Int)`, `nth_error` is `List.getElem?`, `firstn`/`skipn` are
  `List.take`/`List.drop`, `seq 0 n` is `List.range n`, `repeat x n` is
  `List.replicate n x`, `map`/`filter` are `List.map`/`List.filter`, and
  `Forall f l` is `∀ x ∈ l, f x`.  `Some` is `some`.

  Proofs.  A closed decidable proposition closes by `decide`; an equality
  between closed terms of a type with no `DecidableEq` (a `check_result`,
  which carries a `Model`) closes by `rfl` instead.  Both are
  kernel/elaborator reduction rather than compiled evaluation, so the two
  heaviest computations in the file carry their own note at the point
  where they occur.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys

namespace LinuxSem.Checks.Cases.Prelude

-- The specs' `if` chains and the two stack images below are deeper than the
-- default recursion budget admits.
set_option maxRecDepth 1000000

/- =========================================================================
   PART 1 — the EQUIVALENCE definition, on synthetic behaviors

   Trace sets written down by hand, so [Equivalence.equiv]'s verdicts can
   be read off without running a binary.  Per-binary versions of these
   (deriving the trace sets from actual RISC-V images) are the
   per-problem proofs under [Examples/].
   ========================================================================= -/

/-- The program header table the demo binaries publish: `AT_PHDR` at
    `0x10040`, a 56-byte `Elf64_Phdr`, six of them. -/
def demo_phdrs : PhdrInfo := ⟨0x10040, 56, 6⟩

/-- The allocation budget ([State.vm_limit]) these demo checks run
    under: 1 GiB — far above every grant they make, so the budget gate
    is live but never the deciding conjunct except where a check says
    so explicitly (the exhaustion checks below). -/
def demo_limit : Int := 0x40000000

/-- The stack pointer these demo checks are started with: the bottom of
    the SP window, so their grant top ([State.alloc_top]) is the lowest
    any admissible run has and every literal below is admitted by every
    run.  [demo_top] is that top, spelled once. -/
def demo_sp : word := BitVec.ofInt 64 sp_window_lo
def demo_top : Int := sp_window_lo - stack_max_size

/-- The demo ledger's grant ceiling is the SP window's bottom minus the
    model's stack size, whatever the rest of the ledger says. -/
theorem demo_top_is_alloc_top :
    ∀ (reserved : List (word × word)) brk0 mbase lim inp,
      alloc_top (m_vmmaps (init_model reserved brk0 mbase demo_sp lim inp))
      = demo_top := by
  intro reserved brk0 mbase lim inp
  rfl

/-- The process input ([State.ProcInput]) the checks below run on: no
    arguments and no environment, because nothing below reads either.
    That leaves the file system and the standard-input stream, which a
    few checks do vary, as the only two things a call site states.
    Every check that needs no arguments goes through this name, so a new
    [State.ProcInput] field costs those call sites nothing.  The
    exceptions write [mkProcInput] out in full because they need a
    NONEMPTY argv, and they fall into two groups rather than being a list
    worth enumerating: the undecodable-image checks in part 1
    ([run_of_undecodable_image_is_unmodeled],
    [run_of_undecodable_image_refutes_modeled]), and every statement in
    part 6 of [Checks.Examples].  Part 6 needs a nonempty argv because
    [Run.valid_argv] requires at least one argument, so [Run.valid_input]
    is unprovable for the empty argv [demo_input] supplies, and
    [Checks.Examples.demo_input_valid] is where a one-element argv is
    discharged instead.  Part 6's statements that carry no validity
    premise of their own still spell it out, because what they need is
    the SAME input that lemma is about.
    Named as a rule rather than a list: the second group grows with every
    check that has to name part 6's input.

    The launching user is an ORDINARY one, not root, so every check
    below runs unprivileged — that is what makes
    [State.creds_privileged] false for them and keeps the privileged
    credential arms to the checks that build a root model by name.  The
    group is a DIFFERENT number from the user on purpose: a state where
    the two coincide cannot tell a [getgid] wired to [cr_uid] from one
    wired to [cr_gid].

    The accept queue is [State.net_silent]: every peer connects, sends
    nothing and closes.  A check that needs a connection with content
    names its own queue rather than varying this one. -/
def demo_uid : word := BitVec.ofInt 64 1000
def demo_gid : word := BitVec.ofInt 64 1002

/-- The AT_HWCAP word the fixtures launch with.  [Run.valid_hwcap]
    admits two, and the fixtures take the one WITHOUT V — not because
    the model prefers it, but because these checks are about other
    things and the V-carrying mask would make every one of them a
    statement about vector dispatch.  The check that the other mask is
    equally admitted is [valid_hwcap_admits_both_masks] below, and the
    check that the pair is a pair is
    [the_two_hwcap_masks_are_distinct] beside it. -/
def demo_hwcap : word := hwcap_rv64gc

/-- A demo AT_RANDOM draw (the [ed_random] half of [Run.ExecEntry]'s [en_draw]).  Every one of
    the sixteen bytes it serializes to is DIFFERENT, and none of them is
    zero: a fixture whose bytes repeated, or which were all zero, could
    not tell a check that reads byte [k] of the block from one that
    reads byte [j], nor either from one that reads zeros.  Any [bv 128] is a draw the kernel
    can make ([Run.mi_random] carries no validity predicate), so the
    only thing a fixture value has to be is DISTINGUISHING. -/
def demo_random : BitVec 128 :=
  BitVec.ofInt 128 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0

/-- A demo slack draw ([StackLayout.ed_slack]): the bytes of the entry
    stack's last page above the block.  Every byte is [0xa5] except at
    one address, so the checks below can tell "the model reads the draw
    at THIS address" from "the model reads some constant", and the
    NEGATIVE check has a witness that no fixed value fits.  Nothing in
    the model constrains this function; a kernel could leave any bytes
    there ([StackLayout.EntryDraw]).

    The special byte is the guard `(a.toNat % 4096) == 4095`: an equality
    on the unsigned value's remainder, which is what the fixture is
    about. -/
def demo_slack : word → byte :=
  fun a => if (a.toNat % 4096) == 4095 then BitVec.ofInt 8 0x5a
           else BitVec.ofInt 8 0xa5

/-- The two draws together, and the all-zero draw. -/
def demo_draw : EntryDraw := EntryDraw.mkDraw demo_random demo_slack
def zero_draw : EntryDraw :=
  EntryDraw.mkDraw (BitVec.ofInt 128 0) (fun _ => BitVec.ofInt 8 0)

/-- THREE supplementary groups, ascending, and none of them 3.  The
    number [getgroups] reports is the LENGTH of this list, so a fixture
    whose length coincided with one of its elements — or with a uid, a
    gid, or the size argument a check passes — could not tell the model
    that counts from one that reports a member.  Ascending because that
    is the order the kernel stores ([groups_sort] runs inside
    [setgroups], and [groups_to_user] copies the stored order out), so
    this is a list a real [struct group_info] could hold. -/
def demo_groups : List word :=
  [BitVec.ofInt 64 27, BitVec.ofInt 64 1002, BitVec.ofInt 64 4000]

def demo_input (fs0 : Fs.Fs) (stdin0 : InputStream) : ProcInput :=
  mkProcInput [] [] fs0 stdin0 demo_uid demo_gid demo_groups net_silent
              default_nofile (BitVec.ofInt 64 0) demo_hwcap false .Sv48

/-- The same, with a DECLARED PRIVATE /tmp beside the image
    ([State.in_tmp]): the entries are keyed by their one component, and
    [State.init_model] seeds them under "/tmp/" ([State.fs_seed_tmp]).
    [demo_input] is this one with the empty declaration, which
    [State.fs_seed_tmp_nil] makes the image itself. -/
def demo_input_tmp (fs0 tmp0 : Fs.Fs) (stdin0 : InputStream) : ProcInput :=
  ProcInput.mkProcInput_full [] [] fs0 stdin0 demo_uid demo_gid demo_groups
                   net_silent default_nofile (BitVec.ofInt 64 0) demo_hwcap false
                   .Sv48 default_urandom tmp0

/-- The credentials [demo_input] produces: an ordinary user whose real,
    effective and saved ids all agree, because [State.init_model] derives
    the effective and saved ones from the real one it is given. -/
def demo_creds : Creds :=
  Creds.mkCreds demo_uid demo_uid demo_uid demo_gid demo_gid demo_gid demo_groups

/-- [iovcnt32] is the identity below [IOV_MAX]: the low 32 bits of a count
    that already fits in them are the count. -/
theorem iovcnt32_small (w : word) (H : (w.toNat : Int) ≤ IOV_MAX) :
    iovcnt32 w = w := by
  have hw : w.toNat ≤ IOV_MAX.toNat := by
    have := H
    simp only [IOV_MAX] at this
    omega
  have hIOV : IOV_MAX = 1024 := rfl
  have hw' : w.toNat ≤ 1024 := by rw [hIOV] at hw; exact hw
  have hmod : w.toNat % 2 ^ 32 = w.toNat := Nat.mod_eq_of_lt (by omega)
  unfold iovcnt32 Sys.Syscall.abi_low32
  simp only [hmod]
  simp

/-- A byte map answering for exactly the bytes of [bs] laid out from
    [base] upward, and [None] everywhere else.  The lower bound is not
    decoration: without it every address below [base] subtracts to a
    negative [Int], which [Int.toNat] takes to 0, so the map would answer
    the FIRST byte of [bs] for the whole address space below it. -/
def bytes_at (base : word) (bs : List byte) : word → Option byte :=
  fun a => if bv_leu base a
           then bs[((a.toNat : Int) - (base.toNat : Int)).toNat]?
           else none

def mem_ab : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 97 else if bv_eqb a 4097 then some 98 else none

/-- One write("ab")... -/
def cap_boundary_iovecs : List (word × word) :=
  [(4096, BitVec.ofInt 64 (MAX_RW_COUNT - 16)),
   (8192, BitVec.ofInt 64 100),
   (12288, BitVec.ofInt 64 50)]

theorem cap_iovecs_truncates_in_place_and_keeps_the_tail :
    cap_iovecs cap_boundary_iovecs
    = [(4096, BitVec.ofInt 64 (MAX_RW_COUNT - 16)),
       (8192, BitVec.ofInt 64 16),
       (12288, BitVec.ofInt 64 0)]
    ∧ iovs_total (cap_iovecs cap_boundary_iovecs) = MAX_RW_COUNT := by
  constructor <;> decide

/-- For readv: an iovec array at 8192 whose FIRST descriptor is well
    formed ({4096, 1}) and whose SECOND is UNREADABLE, the array stopping
    at 8208.  That makes the count the model actually used visible in the
    verdict: one descriptor is fine, two is -EFAULT. -/
theorem unmodeled_syscall_is_error :
    check_syscall (SyscallInput.mkInput 166 [0, 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
      (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
    = .CheckUnmodeled := by
  rfl

/-- A read on a nonexistent fd fails with -EBADF — a modeled kernel
    failure, NOT a model error — and is not allowed to SUCCEED. -/
def one_map_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 demo_limit)
              (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))

/-- An unaligned addr or len = 0 is -EINVAL, as on Linux. -/
def near_ceiling_sum_model : Model :=
  with_vmmaps
    (mkVmMaps [] [(BitVec.ofInt 64 (two_pow_64 - 8192), 4096)] 0 0 demo_limit)
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))

/-- Reason 3.  A live mapping at [addr + n = 2^64 - 4096], one page
    short of the word's end: [munmap_near_max_is_einval] shows the
    [TASK_SIZE] gate answers -EINVAL there before the exact-match arm
    can see it.  No real
    run ever places a live mapping this close to [2^64] (every range
    Linux hands back sits far below [State.alloc_top]), so only a
    hand-built model can exercise the gate at its own boundary. -/
def noaccess_base : Model := init_model [] 0 0 demo_sp 16384 (demo_input [] IEof)

def noaccess_three_pages : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(65536, 12288)] [(65536, 12288)] 0 0 16384 0 demo_sp)
    noaccess_base

/-- Reason 3.  A fresh PROT_NONE grant lands in BOTH ledgers: [vm_maps]
    owns and budgets it, [vm_noaccess] records that its overlay is absent.
    A user program sees only the consequences; only this states the pair
    of ledgers the grant produces. -/
def stale_overlay (a : word) : Option byte :=
  if bv_eqb a 65536 then some 42 else none

def noaccess_unowned : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull [] [] [(65536, 4096)] 0 0 16384 0 demo_sp) noaccess_base

def noaccess_image_overlap : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull [(4096, 4096)] [(4096, 4096)] [] 0 0 16384 0 demo_sp)
              (init_model [(4096, 4096)] 0 0 demo_sp 16384 (demo_input [] IEof))

def tight_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192)
              (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

def ceiling_room_model : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 demo_limit) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))

def region_live_model : Model :=
  with_vmmaps (mkVmMaps [] [(131072, 4096)] 0 0 demo_limit)
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))

/-- [region_free], independent of the ceiling and the budget (both
    generous here: [demo_limit], and the sole live map is 4096 bytes
    against a [demo_limit] budget).  A grant immediately ADJACENT to the
    live mapping [131072, 135168) — [135168, 139264) — is disjoint and
    grants. -/
theorem fd_truncation_high_low_halves_all_ebadf :
    ∀ fd ∈ [BitVec.ofInt 64 (2 ^ 31), BitVec.ofInt 64 (2 ^ 32 - 1),
            BitVec.ofInt 64 (2 ^ 64 - 1), BitVec.ofInt 64 (2 ^ 63 + 2 ^ 32 - 1)],
      check_syscall (SyscallInput.mkInput 64 [fd, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
        (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
      = .CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [] := by
  intro fd hfd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfd
  rcases hfd with h | h | h | h <;> subst h <;> rfl

/-- ...while a LIVE low half is reached however enormous the register:
    fd = 2^63 is stdin, so a write to it is -EBADF for the RIGHT reason
    (stdin is read-only, [FdChannel 0]) and a read from it is a stdin
    read — at end of input, 0.  Channel direction is an assumption
    about the environment rather than a property of the fd number. -/
theorem fd_truncation_live_low_half_under_bit63 :
    check_syscall (SyscallInput.mkInput 64 [BitVec.ofInt 64 (2 ^ 63), 4096, 2, 0, 0, 0]
                     mem_ab (fun _ => none))
      (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
    = .CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
    ∧ check_syscall (SyscallInput.mkInput 63 [BitVec.ofInt 64 (2 ^ 63), 4096, 16, 0, 0, 0]
                       (fun _ => none) (fun _ => none))
         (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
       = .CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [] := by
  constructor <;> rfl

/-- The value that comparison runs against — pinned as a numeral, so a
    switch of [fd32] to SIGN-extension (which would make [AT_FDCWD32] the
    full-width -100 again) cannot pass unnoticed.  No trace can present a
    model constant, so nothing but this example pins it. -/
theorem at_fdcwd32_is_the_low_half_of_minus_100 :
    AT_FDCWD32 = BitVec.ofInt 64 4294967196 := by
  decide

/-- Truncation does not widen AT_FDCWD to "any dirfd whose low half looks
    plausible": a LIVE fd as dirfd is still an unmodeled
    relative-to-a-dirfd open, and still fails closed. -/
def wpast_model : Model :=
  mkModel [(3, FdEntry.FdFileW [102] 4)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104, 105])]

/-- write(3, buf, 0) at that offset transfers nothing and leaves both the
    file and the fd offset alone, as on Linux.  [Fs.file_write] does not
    zero-extend the file out to the offset here. -/
def rlim_bytes (soft hard : byte) : List byte :=
  [soft, 0, 0, 0, 0, 0, 0, 0, hard, 0, 0, 0, 0, 0, 0, 0]

/-- A writable 16-byte landing zone at 4096 for the read's out-parameter. -/
def rlim_out : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4112 then some 0 else none

/-- A readable source struct at 8192, for the set arm. -/
def rlim_src_at (soft hard : byte) : word → Option byte :=
  fun a => if bv_ltu a 8192 then none
           else if bv_eqb a 8192 then some soft
           else if bv_ltu a 8200 then some 0
           else if bv_eqb a 8200 then some hard
           else if bv_ltu a 8208 then some 0
           else none

def rlim_model : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)

/-- A NONZERO soft limit on purpose: it is what lets the set below
    actually change the record, so [prlimit64_read_after_set] cannot pass
    by accident. -/
def rlim_pinned : Model := with_rlimit_core (rlim_bytes 3 7) rlim_model

/- ---- uname (160) -------------------------------------------------------- -/

/-- A 390-byte writable landing zone at 4096 for [uname]'s only
    out-parameter.  Deliberately EXACT: [uts_out_short] below is the same
    zone one byte shy, which is the shape that separates the -EFAULT arm
    from the decline. -/
def uts_out : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4486 then some 0 else none

def uts_out_short : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4485 then some 0 else none

/-- Six members, assembled the way the kernel's struct is laid out. -/
def uts_name_of (nodename release version domainname : List Int) : List byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal nodename
  ++ uts_literal release
  ++ uts_literal version
  ++ uts_literal uts_machine_chars
  ++ uts_literal domainname

/-- "6.18.46" and "6.1.0" — two RELEASE strings, both inside the
    envelope.  Which one a machine reports is not something the kernel
    source settles, so neither is privileged; what the examples below use
    them for is that a run may report one of them and then must go on
    reporting THAT one. -/
def uts_release_a : List Int := [54, 46, 49, 56, 46, 52, 54]
def uts_release_b : List Int := [54, 46, 49, 46, 48]

def uts_demo   : List byte := uts_name_of [] uts_release_a [] []
def uts_demo_b : List byte := uts_name_of [] uts_release_b [] []

/-- A name Linux cannot hold: [sysname] reading "Linuy".  Nothing writes
    that member after [init_uts_ns], so the literal is the only value it
    takes. -/
def uts_bad_sysname : List byte :=
  uts_literal [76, 105, 110, 117, 121]
  ++ uts_literal [] ++ uts_literal uts_release_a ++ uts_literal []
  ++ uts_literal uts_machine_chars ++ uts_literal []

/-- A [release] with no terminator inside its 65 bytes — every byte
    'A'.  [Kernel.Sys.utsname_wf] leaves the release's CONTENT free and
    still refuses this, which is what makes the terminator conjunct
    separately testable. -/
def uts_unterminated_release : List byte :=
  uts_literal uts_sysname_chars ++ uts_literal []
  ++ List.replicate 65 (BitVec.ofInt 8 65)
  ++ uts_literal [] ++ uts_literal uts_machine_chars ++ uts_literal []

def uts_model : Model := rlim_model
def uts_pinned : Model := with_utsname uts_demo uts_model

/-- The last four bytes of the address space, so the 390-byte copy-out
    covers them and then 386 more at 0 — the shape
    [State.read_bytes_map]'s wrapping walk accepts and
    [State.access_okb]'s [Int] subtraction refuses.  Same construction as
    [Checks.Cases.Fs.Pipe]'s [pipe2_wrap_fildes] and
    [Checks.Cases.Net.Socket]'s socketpair group. -/
def uts_wrap_name : word := BitVec.ofInt 64 (2 ^ 64 - 4)

def uts_wrap_mem : word → Option byte :=
  fun a => if ((a.toNat < 386) || (2 ^ 64 - 4 ≤ a.toNat))
           then some (BitVec.ofInt 8 0) else none

/- =========================================================================
   PART 2 — the shared fixtures, read back off the model
   ========================================================================= -/

/-- The FIRST read is where the environment's inherited limit enters the
    model: any well-formed pair is admissible, and it becomes the pin. -/
theorem argc_zero_invalid : ¬ valid_argv [] := by
  intro H
  have h := H.1.1
  simp at h

theorem argv_single_empty_string_valid : valid_argv [[]] := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    decide
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    decide
  · simp

/-- The auxv's AT_RANDOM entry carries [at_random_ptr], and the 16 bytes
    there are materialized in the initial stack image (a libc seeding its
    stack canary from AT_RANDOM dereferences the pointer).  What is
    materialized is THIS RUN'S DRAW, the [ed_random] half of
    [Run.ExecEntry]'s [en_draw], laid
    down little-endian; the expected list is written out as literal
    bytes rather than as [at_random_bytes demo_random], so that the check
    pins the serialization and the placement together instead of
    restating the definition.  Checked on a concrete layout:
    argv = ["x"], envp = []. -/
theorem at_random_points_at_the_16_drawn_bytes :
    let sp : word := 65536
    let mem := stack_to_mem sp
                 (build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap
                    demo_draw)
    (List.range 16).map (fun k => mem (at_random_ptr sp [[120]] [] + nat_to_word k))
  = (List.map (fun b => some (BitVec.ofInt 8 b))
        [0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87,
         0x78, 0x69, 0x5a, 0x4b, 0x3c, 0x2d, 0x1e, 0x0f]) := by
  decide

/-- The same read at the ZERO draw returns zeros.  Keeping both halves is the point
    of the pair: the check above alone would still pass if the block were
    some other fixed constant, and this one alone would still pass if the
    block were fixed at zero. -/
theorem at_random_points_at_zeros_at_the_zero_draw :
    let sp : word := 65536
    let mem := stack_to_mem sp (build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap zero_draw)
    (List.range 16).map (fun k => mem (at_random_ptr sp [[120]] [] + nat_to_word k))
  = List.replicate 16 (some (BitVec.ofInt 8 0)) := by
  decide

/-- The draw moves those 16 bytes and NOTHING ELSE: at two draws the
    images have equal prefixes and the tail is the draw's own bytes.
    [StackLayout.build_stack_bytes_split_random] says this for every
    argument; here it is on a concrete layout, where the prefix equality
    is a computation rather than a unification side condition. -/
theorem at_random_block_is_all_the_draw_moves :
    let sp : word := 65536
    let bs  := build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap demo_draw
    let bs0 := build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap zero_draw
    (List.take (bs.length - 16) bs, List.drop (bs.length - 16) bs)
  = (List.take (bs0.length - 16) bs0, at_random_bytes demo_random) := by
  decide

/-- The NEGATIVE half: a proof may NOT assume the block is zero.  If
    [at_random_bytes] were [repeat (Z_to_bv 8 0) 16], this statement
    would be a theorem and every equivalence proof could compute through
    it.  A binary that echoes its AT_RANDOM bytes would then be modeled
    as echoing zeros, so it could be proved equivalent to one that
    really does write sixteen zeros, which is false on almost every real
    run.  The statement is refutable, by the draw the kernel is equally
    free to make. -/
theorem zero_at_random_block_is_refuted :
    ¬ (∀ (sp : word) rnd,
       (build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap rnd).drop
             ((build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap rnd).length - 16)
       = List.replicate 16 (BitVec.ofInt 8 0)) := by
  intro H
  have h := H (BitVec.ofInt 64 65536) demo_draw
  exact absurd h (by decide)

/- ---- the page the entry stack image ends in ------------------------ -/

/-- The demo layout, spelled once: argv = ["x"], envp = [], a
    page-aligned [sp] so the page boundary above the block is easy to
    read off.  The block is what [build_stack_bytes] lays out; the model
    maps up to the next page boundary above it. -/
def h_sp : word := BitVec.ofInt 64 65536
def h_block : List byte :=
  build_stack_bytes demo_phdrs h_sp [[BitVec.ofInt 8 120]] [] demo_uid demo_hwcap
    demo_draw
def h_mem (draw : EntryDraw) : word → Option byte :=
  (init_machine_state [] 0x10000 demo_phdrs h_sp draw
     [[BitVec.ofInt 8 120]] [] demo_uid demo_hwcap).ms_mem

/-- THE POSITIVE HALF.  The first byte above the block, the last byte of
    the page it ends in, and the first byte above that page.  The first
    two are mapped and carry the entry's [ed_slack] draw at their own
    address — [demo_slack] answers 0x5a at an address one below a page
    boundary and 0xa5 elsewhere, so the pair also pins that the model
    reads the draw AT THE ADDRESS rather than at some fixed offset.  The
    third is unmapped, which is where the model stops, although a real
    stack VMA goes on above it: a known limitation of the model (see the
    note above [Run.entry_block_top]).

    If the FIRST of these were [None] too, a load there would be a
    fault the model produces and no kernel does. -/
theorem entry_page_above_the_block_is_mapped :
    (h_mem demo_draw (BitVec.ofInt 64 (entry_block_top h_sp h_block)),
     h_mem demo_draw (BitVec.ofInt 64 (entry_page_top h_sp h_block - 1)),
     h_mem demo_draw (BitVec.ofInt 64 (entry_page_top h_sp h_block)))
  = (some (BitVec.ofInt 8 0xa5), some (BitVec.ofInt 8 0x5a), none) := by
  decide

/-! ### The whole slack region is mapped

    The claim is that every byte of the entry stack's slack region — the
    rest of the page the block ends in — is mapped.  `decide` over the
    3,880-element `List.range` is not a route this file can take: each
    element reads `h_mem` at its own address, the `stack_to_mem` behind
    it walks the image to that index, and the kernel interpreter needs
    roughly 7.5M steps for the `forallb`.  That exhausts the stack before
    any heartbeat budget, and `native_decide` would add a postulate, which
    this tree does not do.  So the check is proved for a SYMBOLIC index:
    the only list facts it uses are the block's length, the slack's
    length, and `List.getElem?_eq_none_iff` on the byte map's in-range
    branch.

    The fixture's sizes are read off `build_stack_bytes`'s length
    skeleton (`simp only` over the appends and the 16-byte draw block),
    NOT by reducing the 216-byte block itself: `decide` on the latter
    overflows the default recursion budget, the same interpreter limit
    the paragraph above records.  Those sizes put the slack at the image
    indices `block.length + k` for `k < entry_slack_len`, which is what
    makes the per-byte step structural rather than a page-wide walk. -/

/-- The block's length, from the layout's length skeleton.  Unfolding the
    block itself is what overflows `decide`, so the proof rewrites through
    the appends instead. -/
private theorem h_block_length : h_block.length = 216 := by
  show (build_stack_bytes demo_phdrs h_sp [[120]] [] demo_uid demo_hwcap demo_draw).length = 216
  simp only [build_stack_bytes, len_word, string_addrs, flatten_strings,
    length_auxv_bytes, auxv_size, length_at_random_bytes, word_le8,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod]

/-- The fixture's stack pointer as an unsigned value. -/
private theorem h_sp_unsigned : h_sp.toNat = 65536 := by
  decide

/-- The block's top address. -/
private theorem h_block_top : entry_block_top h_sp h_block = 65752 := by
  unfold entry_block_top
  rw [h_sp_unsigned, h_block_length]
  omega

/-- The slack length: the page boundary above the block, less the block's
    top. -/
private theorem h_slack_length : entry_slack_len h_sp h_block = 3880 := by
  unfold entry_slack_len entry_page_top page_round_up_Z page_size
  rw [h_block_top]
  decide

/-- The image ends exactly at the page boundary. -/
private theorem h_image_length :
    (h_block ++ entry_slack h_sp h_block demo_slack).length = 4096 := by
  rw [List.length_append, length_entry_slack, h_block_length, h_slack_length]

/-- A SYMBOLIC index into the slack is a mapped address: the image holds
    `block.length + k` for every `k < entry_slack_len`, and the byte map's
    in-range branch answers `some` there.  No element is enumerated, so
    the 3,880-byte walk never enters the kernel. -/
private theorem stack_to_mem_slack_mapped (k : Nat)
    (hk : k < entry_slack_len h_sp h_block) :
    stack_to_mem h_sp (h_block ++ entry_slack h_sp h_block demo_slack)
      (BitVec.ofInt 64 (entry_block_top h_sp h_block + (k : Int))) ≠ none := by
  let a : word := BitVec.ofInt 64 (entry_block_top h_sp h_block + (k : Int))
  change stack_to_mem h_sp (h_block ++ entry_slack h_sp h_block demo_slack) a ≠ none
  have hk' : k < 3880 := by
    rw [← h_slack_length]
    exact hk
  have hz : 0 ≤ entry_block_top h_sp h_block + (k : Int) := by
    rw [h_block_top]
    omega
  have hlt : entry_block_top h_sp h_block + (k : Int) < two_pow_64 := by
    rw [h_block_top]
    have h2 : two_pow_64 = (18446744073709551616 : Int) := by decide
    rw [h2]
    omega
  have haval : (a.toNat : Int) = entry_block_top h_sp h_block + (k : Int) :=
    bv_unsigned_Z_to_bv_u64 _ ⟨hz, hlt⟩
  rw [h_block_top] at haval
  have hle : h_sp.toNat ≤ a.toNat := by
    rw [h_sp_unsigned]
    omega
  have hoffZ : (a.toNat : Int) - (h_sp.toNat : Int) = (216 : Int) + (k : Int) := by
    rw [h_sp_unsigned]
    omega
  have hoffnat : ((a.toNat : Int) - (h_sp.toNat : Int)).toNat = 216 + k := by
    rw [hoffZ]
    rw [show (216 : Int) + (k : Int) = ((216 + k : Nat) : Int) from by
      rw [Int.natCast_add]
      rfl]
    rw [Int.toNat_natCast]
  have hofflt : (a.toNat : Int) - (h_sp.toNat : Int)
      < ((h_block ++ entry_slack h_sp h_block demo_slack).length : Int) := by
    rw [hoffZ, h_image_length]
    omega
  intro hnone
  unfold stack_to_mem at hnone
  rw [ite_eq_left hle] at hnone
  dsimp only at hnone
  rw [ite_eq_left hofflt] at hnone
  rw [List.getElem?_eq_none_iff] at hnone
  omega

/-- `h_mem` is the entry-image byte map with the model's zero-fill overlay;
    at an address the image holds, the overlay is not reached. -/
private theorem h_mem_eq_stack (draw : EntryDraw) (addr : word) :
    h_mem draw addr =
      (match stack_to_mem h_sp
          (entry_stack_image demo_phdrs h_sp [[120]] [] demo_uid demo_hwcap draw) addr with
       | some b => some b
       | none =>
         if decide ((h_sp.toNat : Int) - stack_max_size ≤ (addr.toNat : Int)) &&
            decide ((addr.toNat : Int) < (h_sp.toNat : Int))
         then some (BitVec.ofInt 8 0) else none) := rfl

/-- THE SLACK, EVERY BYTE.  The whole-page companion of
    `entry_page_above_the_block_is_mapped`, which pins the first byte, the
    last byte of the page and the byte above it; here the quantification
    is over every slack index at once and closes through the per-byte
    lemma above. -/
theorem every_byte_of_the_entry_page_is_mapped :
    (List.range (entry_slack_len h_sp h_block)).all
      (fun k => (h_mem demo_draw
        (BitVec.ofInt 64 (entry_block_top h_sp h_block + (k : Int)))).isSome) = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hne : stack_to_mem h_sp
      (entry_stack_image demo_phdrs h_sp [[120]] [] demo_uid demo_hwcap demo_draw)
      (BitVec.ofInt 64 (entry_block_top h_sp h_block + (k : Int))) ≠ none := by
    rw [show entry_stack_image demo_phdrs h_sp [[120]] [] demo_uid demo_hwcap demo_draw
        = h_block ++ entry_slack h_sp h_block demo_slack from rfl]
    exact stack_to_mem_slack_mapped k hk
  rw [h_mem_eq_stack]
  cases hs : stack_to_mem h_sp
      (entry_stack_image demo_phdrs h_sp [[120]] [] demo_uid demo_hwcap demo_draw)
      (BitVec.ofInt 64 (entry_block_top h_sp h_block + (k : Int))) with
  | none => exact absurd hs hne
  | some b => rfl

/-- The region is not empty, so the two checks above are about something:
    for this layout the block ends mid-page and the slack is the rest of
    it. -/
theorem the_entry_page_slack_is_not_empty :
    (entry_slack_len h_sp h_block == 0) = false := by
  decide

/-- THE NEGATIVE HALF, and the one that keeps the region a CHOICE.  A
    proof may not assume the bytes above the block are zero — nor any
    other fixed value, since the draw is unconstrained and quantified per
    binary.  Zeros are what a model that page-filled instead of drawing
    would give, and what Linux leaves only in the part of the region
    nothing wrote: which part that is depends on the exec filename's
    length, which this model does not carry
    ([StackLayout.EntryDraw]). -/
theorem zero_entry_page_slack_is_refuted :
    ¬ (∀ draw : EntryDraw,
       h_mem draw (BitVec.ofInt 64 (entry_block_top h_sp h_block))
       = some (BitVec.ofInt 8 0)) := by
  intro H
  have h := H demo_draw
  exact absurd h (by decide)

/-- The other direction of the same claim: two draws that differ only in
    the slack give different bytes up there, and the SAME bytes
    everywhere the kernel wrote.  So the draw is live, and no address in
    the layout moves with it
    ([Run.entry_stack_image_block_prefix] for every argument). -/
theorem the_slack_draw_does_not_move_the_block :
    build_stack_bytes demo_phdrs h_sp [[BitVec.ofInt 8 120]] [] demo_uid demo_hwcap
      (EntryDraw.mkDraw demo_random (fun _ => BitVec.ofInt 8 0))
    = h_block := by
  decide

theorem two_slack_draws_disagree_above_the_block :
    h_mem (EntryDraw.mkDraw demo_random (fun _ => BitVec.ofInt 8 0))
          (BitVec.ofInt 64 (entry_block_top h_sp h_block))
    ≠ h_mem demo_draw (BitVec.ofInt 64 (entry_block_top h_sp h_block)) := by
  intro H
  exact absurd H (by decide)

/-- The pointer really is what the auxv slot stores: reading the value
    half of the AT_RANDOM entry back out of the image yields
    [at_random_ptr] (the entry sits 3 slots -- 24 bytes -- before the
    end of the [auxv_size]-byte auxv, which ends the struct prefix). -/
theorem at_random_auxv_slot_stores_the_pointer :
    let sp : word := 65536
    let bytes := build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap demo_draw
    let auxv_end := (8 + (1 + 1) * 8 + (0 + 1) * 8 + auxv_size)
    List.take 8 (List.drop (auxv_end - 24) bytes)
  = word_le8 (at_random_ptr sp [[120]] []) := by
  decide

/-- THREAD-LOCAL STORAGE hinges on this: a static libc finds PT_TLS only
    by walking the program header table, and finds the table only through
    AT_PHDR/AT_PHENT/AT_PHNUM.  The three entries are the first three
    auxv slots, so their (type, value) words are the first six words of
    the auxv, which starts right after argc, the argv pointers (+ NULL)
    and the envp pointers (+ NULL).  Read them straight back out of the
    initial stack image and check they carry the IMAGE's numbers, not
    zeros. -/
theorem auxv_publishes_the_program_header_table :
    let sp : word := 65536
    let bytes := build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap demo_draw
    let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)
    (List.range 6).map (fun k => List.take 8 (List.drop (auxv_start + 8 * k) bytes))
  = [ word_le8 AT_PHDR,  word_le8 (BitVec.ofInt 64 0x10040),
      word_le8 AT_PHENT, word_le8 (BitVec.ofInt 64 56),
      word_le8 AT_PHNUM, word_le8 (BitVec.ofInt 64 6) ] := by
  decide

/-- AT_UID / AT_EUID carry THE RUN'S OWN USER, and the same one the
    credential readers answer.  Linux ties those two together by reading
    one field twice: [create_elf_tables] (fs/binfmt_elf.c) emits
    [NEW_AUX_ENT(AT_UID, from_kuid_munged(cred->user_ns, cred->uid))]
    off [cred = current_cred()], and [SYSCALL_DEFINE0(getuid)]
    (kernel/sys.c) returns [from_kuid_munged(current_user_ns(),
    current_uid())], where [current_uid()] IS [current_cred()->uid] —
    both texts read off Linux v6.18.46 (commit 1f99e9ab748f) and
    byte-identical there and at every mainline release tag from v4.4
    through v6.18.  So a program that reads AT_UID off its own initial
    stack and compares it with [getuid()] always sees them agree, and a
    model that let them differ would
    describe a process no kernel produces.

    NO SYSCALL CHECK REACHES THIS.  The syscall checker folds over the
    syscalls of a run; it never builds the model's initial stack, so
    the auxv side is invisible to it.  The three checks below are the
    evidence instead.

    Read back out of the built image, the way the program header entries
    are above: AT_UID is the SIXTH auxv entry and AT_EUID the seventh —
    AT_HWCAP sits fourth, ahead of AT_PAGESZ, where
    [create_elf_tables] puts it — so their (type, value) words are words
    10..13 of the vector. -/
theorem auxv_publishes_the_launching_uid :
    let sp : word := 65536
    let bytes := build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap demo_draw
    let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)
    (List.range 4).map (fun k => List.take 8 (List.drop (auxv_start + 8 * (10 + k)) bytes))
  = [ word_le8 AT_UID,  word_le8 demo_uid,
      word_le8 AT_EUID, word_le8 demo_uid ] := by
  decide

/-- …for EVERY uid, not just [demo_uid]: the two id entries are exactly
    the launching one, and there is no third entry a uid could hide in.
    Universally quantified, so no finite set of traces could establish
    it. -/
theorem auxv_ids_are_exactly_the_launching_uid (ph : PhdrInfo) (at_random uid hw : word) :
    (auxv_entries ph at_random uid hw).filter
      (fun e => bv_eqb e.1 AT_UID || bv_eqb e.1 AT_EUID)
    = [(AT_UID, uid), (AT_EUID, uid)] := by
  rfl

/-- …and that uid is the one the READERS answer, not a second copy that
    could drift from it: both entries hold the credentials
    [State.init_model] builds, which is what [Kernel.Sys.getid_spec]
    projects.  This is the whole argument — one source, so the two
    cannot disagree. -/
theorem auxv_ids_are_the_credentials_the_readers_answer :
    ∀ (reserved : List (word × word)) brk0 mbase sp lim inp ph at_random,
      auxv_entries ph at_random inp.in_uid inp.in_hwcap
      = [ (AT_PHDR,   BitVec.ofInt 64 (ph.ph_addr : Int)),
          (AT_PHENT,  BitVec.ofInt 64 (ph.ph_ent : Int)),
          (AT_PHNUM,  BitVec.ofInt 64 (ph.ph_num : Int)),
          (AT_HWCAP,  inp.in_hwcap),
          (AT_PAGESZ, BitVec.ofInt 64 4096),
          (AT_UID,    (m_creds (init_model reserved brk0 mbase sp lim inp)).cr_uid),
          (AT_EUID,   (m_creds (init_model reserved brk0 mbase sp lim inp)).cr_euid),
          (AT_SECURE, BitVec.ofInt 64 0),
          (AT_RANDOM, at_random),
          (AT_NULL,   BitVec.ofInt 64 0) ] := by
  intro reserved brk0 mbase sp lim inp ph at_random
  rfl

/-- ** AT_HWCAP: the entry, its range, and what the range excludes

    AT_HWCAP is the one auxv value that is neither the image's nor the
    launching user's: it describes the HART.  [Run.valid_hwcap] admits
    two words and no more, and the checks below are what say that the
    pair is a pair — that both members are really admitted, that the
    entry really carries the launch's word, and that the model refuses
    the masks a kernel would not publish.  The kernel argument for
    exactly these two is in [StackLayout]'s AT_HWCAP bullet.

    NO SYSCALL CHECK REACHES THESE, for the same reason the id checks
    above are unreachable: the syscall checker never builds the model's
    initial stack.

    First the entry is THERE, and where Linux puts it: AT_HWCAP is the
    fourth auxv entry, immediately before AT_PAGESZ, so its (type,
    value) words are words 6 and 7 of the vector. -/
theorem auxv_publishes_the_hart_capabilities :
    let sp : word := 65536
    let bytes := build_stack_bytes demo_phdrs sp [[120]] [] demo_uid demo_hwcap demo_draw
    let auxv_start := (8 + (1 + 1) * 8 + (0 + 1) * 8)
    (List.range 4).map (fun k => List.take 8 (List.drop (auxv_start + 8 * (6 + k)) bytes))
  = [ word_le8 AT_HWCAP,  word_le8 demo_hwcap,
      word_le8 AT_PAGESZ, word_le8 (BitVec.ofInt 64 4096) ] := by
  decide

/-- …carrying the LAUNCH'S word, for every launch, and there is no
    second entry a hwcap could hide in.  Universally quantified, so no
    finite set of traces could establish it — the same shape as
    [auxv_ids_are_exactly_the_launching_uid] above. -/
theorem auxv_hwcap_is_exactly_the_launch_word (ph : PhdrInfo) (at_random uid hw : word) :
    (auxv_entries ph at_random uid hw).filter (fun e => bv_eqb e.1 AT_HWCAP)
    = [(AT_HWCAP, hw)] := by
  rfl

/-- BOTH masks are admitted.  Without this the disjunction could have
    been written with an unsatisfiable second arm and every proof would
    still go through, which is exactly the "quantifier that says
    nothing" failure [Equivalence.image_brk_satisfiable] guards against
    elsewhere. -/
theorem valid_hwcap_admits_both_masks :
    valid_hwcap hwcap_rv64gc ∧ valid_hwcap hwcap_rv64gcv :=
  ⟨Or.inl rfl, Or.inr rfl⟩

/-- …and the two are DIFFERENT, so quantifying over them is quantifying
    over something.  Compared on unsigned values, the way
    [the_constant_zero_auxv_is_refuted] below compares vectors. -/
theorem the_two_hwcap_masks_are_distinct :
    (hwcap_rv64gc.toNat : Int) ≠ (hwcap_rv64gcv.toNat : Int) := by
  decide

/-- …and the difference is exactly the V bit, which is the whole claim:
    the six extensions the decoder implements are present in both, and
    the only word that moves is [COMPAT_HWCAP_ISA_V], [1 << ('V' -
    'A')] (arch/riscv/include/uapi/asm/hwcap.h, Linux v6.18.46, commit
    1f99e9ab748f).  Written as an arithmetic identity rather than as two
    literals so that changing either constant without changing the other
    fails here. -/
theorem the_two_masks_differ_in_the_v_bit_alone :
    ((hwcap_rv64gcv.toNat : Int) - (hwcap_rv64gc.toNat : Int)) = (2 ^ 21 : Int) := by
  decide

/-- THE NEGATIVE, first half: the model refuses the word an ABSENT
    entry effectively delivers.  A runtime that looks the type up and
    finds nothing uses its default, zero — a hart with no extensions at
    all, on which none of this model's instructions could run.  Nothing
    in [valid_hwcap] admits it. -/
theorem valid_hwcap_refuses_the_absent_entrys_zero :
    ¬ valid_hwcap (BitVec.ofInt 64 0) := by
  intro H
  rcases H with H | H <;> exact absurd H (by decide)

/-- THE NEGATIVE, second half: it also refuses two words that are
    WRONG IN OPPOSITE DIRECTIONS, which is what makes the pair a range
    rather than a shrug.

    [0x112C] drops the A bit ([COMPAT_HWCAP_ISA_A] is bit 0) from an
    otherwise-RV64GC mask: a hart without atomics, which cannot run the
    [Riscv.Instr] AMOs this semantics interprets, so the model must not
    describe a process on one.  [0x40112D] adds bit 22 — the letter W,
    which [riscv_fill_hwcap]'s [isa2hwcap] never assigns
    (arch/riscv/kernel/cpufeature.c:1059-1065, Linux v6.18.46, commit
    1f99e9ab748f, which seeds seven indices and leaves the other
    nineteen zero), so no kernel publishes it and admitting it would put
    the model outside what that kernel tree can produce. -/
theorem valid_hwcap_refuses_masks_no_kernel_publishes :
    ¬ valid_hwcap (BitVec.ofInt 64 0x112C) ∧ ¬ valid_hwcap (BitVec.ofInt 64 0x40112D) := by
  constructor <;> intro H <;>
    (rcases H with H | H <;> exact absurd H (by decide))

/-- THE NEGATIVE, third half: the nine-entry vector WITHOUT AT_HWCAP is
    not what the model builds.  Stated on the entry TYPES, so it is a
    claim about the entry SET rather than about any value: a model that
    dropped the entry, or moved it behind AT_PAGESZ where Linux does not
    put it, fails here. -/
theorem the_hwcap_less_auxv_is_refuted :
    (auxv_entries demo_phdrs (BitVec.ofInt 64 0) demo_uid demo_hwcap).map
      (fun e => (e.1.toNat : Int))
    ≠ [3, 4, 5, 6, 11, 12, 23, 25, 0] := by
  decide

/-- The entry set the model DOES build, in order, as the positive twin
    of that refutation. -/
theorem the_auxv_entry_types_in_order :
    (auxv_entries demo_phdrs (BitVec.ofInt 64 0) demo_uid demo_hwcap).map
      (fun e => (e.1.toNat : Int))
    = [3, 4, 5, 16, 6, 11, 12, 23, 25, 0] := by
  decide

/-- THE NEGATIVE.  A literal [AT_UID = AT_EUID = 0] for every process
    would make the model admit a trace where [getuid()] disagrees with
    the stack the same process was handed.  Construct that auxv and
    check it is refused: a process
    launched as [demo_uid] does NOT get the vector a root launch gets.
    Compared on unsigned values, so the disagreement is a difference
    between two lists of integers rather than between two [bv] records
    carrying opaque well-formedness proofs. -/
theorem the_constant_zero_auxv_is_refuted :
    (auxv_entries demo_phdrs (BitVec.ofInt 64 0) demo_uid demo_hwcap).map
      (fun e => (e.2.toNat : Int))
    ≠ (auxv_entries demo_phdrs (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) demo_hwcap).map
         (fun e => (e.2.toNat : Int)) := by
  decide

end LinuxSem.Checks.Cases.Prelude
