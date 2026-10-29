/-
  * LinuxProcessSem.Sys.Drivers.Char.Random — getrandom (278)


  This file answers to Linux `drivers/char/random.c`: it holds what
  the kernel defines there, and nothing else.  Which file a spec
  belongs in is therefore not a judgement call — look up where the
  kernel defines the syscall.  `Specs.v` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.v` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  NOTES (notation only, all mechanical):

  - `Z` → `Int`, `bv_unsigned w` → `(w.toNat : Int)`, `Z.eqb` → `==`,
    `Z.leb` inside a `bool` test → `decide (· ≤ ·)`, `negb b` → `!b`,
    `list` → `List`, `byte` → `BitVec 8`, `word` → `BitVec 64`.
  - `Sys SyscallEffect` is `SysSpec SyscallEffect` here (see
    `MonadInstances`), and `x <- c ;; k` is `bind c (fun x => k)`.
  - `ret_only` / `err_ret` / `errno_from` / `w_is0` are
    `Sys/Syscall.lean`'s; `modeled_rw_count` and `delivered_writes` are
    `Sys/Uaccess.lean`'s, opened SELECTIVELY because that file still
    carries staging copies of `ret_only` / `err_ret` (see its NOTE)
    that must not shadow `Sys/Syscall`'s; `GRND_NONBLOCK` / `GRND_RANDOM`
    are `Sys/Uapi.lean`'s; `read_bytes_map` and `access_okb` are
    `StateMemory`'s; `len_word` is `BvBase`'s; `errno_ret` and `mkEffect`
    are `State.lean`'s; `mkModel` is `StateLedger`'s (checks only).
  - The `SyscallEffect` write list is spelled out as `[(buf, bs)]` below,
    on the same reading, rather than through
    `Uaccess.delivered_writes`; the two agree on every NONEMPTY `bs`,
    which is the only shape the write arms here can produce.  The
    zero-byte arm is `ret_only`, i.e. the canonical empty write list.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Uaccess

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi (GRND_NONBLOCK GRND_RANDOM)
open LinuxSem.LinuxProcessSem.Sys.Uaccess
  (rw_bytes_max modeled_rw_count delivered_writes)

namespace LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random

/-! ## getrandom -/

/-- getrandom: only EINTR (the pool-not-ready wait, see the bound's
    comment below), kept admissible for a request above
    `getrandom_small_max` bytes.  The urandom pool is treated as always
    initialized (see the flags note at `getrandom_spec`), EFAULT is the
    fail-closed `unmodeled`, and bad flags are unmodeled. -/
def getrandom_errnos : List Int := [EINTR]

/-- THE SMALL-REQUEST BOUND.  getrandom(2) documents that once the
    pool is initialised a request of up to 256 bytes always returns as
    many bytes as requested and is not interrupted by a signal.  The
    kernel gives more than that.  In `get_random_bytes_user`
    (drivers/char/random.c) the copy loop consults `signal_pending`
    only when `ret % PAGE_SIZE == 0` — after a whole page has landed,
    and only while bytes remain, since the loop breaks first once the
    request is satisfied — and a signal there yields the short positive
    count, never -EINTR.  So the loop cannot cut any request of at most
    a page short, and a request of at most CHACHA_KEY_SIZE bytes never
    enters the loop at all.  Read at Linux v6.12.1 (the break at line
    474, the page test at lines 478-480) and at v7.1.8 (lines 464 and
    468-470), which bracket the v6.18.46 this tree cites and agree in
    control flow; the tree's own version was not read.  The only
    -EINTR is `wait_for_random_bytes`, behind the `crng_ready` gate of
    `SYSCALL_DEFINE3(getrandom, ...)` (v6.12.1 lines 1403-1408, v7.1.8
    lines 1395-1400), entered only while the pool is not yet ready —
    which the flags note at `getrandom_spec` already assumes never
    happens once user code runs.  The bound is 256 rather than a page
    because getrandom(2)'s documented guarantee is what programs rely
    on: the spec claims of the kernel no more than the contract does.
    A request at or under this bound is delivered in full: see the
    small-request arm of `getrandom_spec`. -/
def getrandom_small_max : Int := 256

/-- `getrandom buf buflen flags`: environment bytes, but a nonzero
    request never "succeeds" with zero bytes.  Real getrandom blocks
    until it can deliver at least one byte, so a 0 return happens only
    for `buflen = 0` — consistent with the channel-read branch's >= 1
    lower bound.  A nonzero request of at most `getrandom_small_max`
    bytes is delivered IN FULL and is never interrupted (the bound's
    comment says why): the only outcome is `buflen` environment-chosen
    bytes and a return of `buflen`.  Above that bound the delivered
    count stays environment-chosen in `[1, buflen]` (a signal can
    interrupt a large request after some bytes), beside the -EINTR
    alternative.  The zero-byte success carries no write entry (the
    canonical zero-byte shape, see `Uaccess.delivered_writes`); the
    zero-byte arm keeps its interrupted alternative and is not narrowed
    here.

    Flags: 0 and GRND_NONBLOCK are accepted and treated identically —
    on any modern kernel the urandom pool is initialized long before
    user code runs, so GRND_NONBLOCK never changes the outcome of an
    urandom read.  GRND_RANDOM (the blocking /dev/random pool) and any
    unknown flag bit are unmodeled: `unmodeled`, fail closed.  That
    includes a set high half, which is a narrowing rather than a
    disagreement: `flags` is `unsigned int` at the boundary
    (`SYSCALL_DEFINE3(getrandom, ...)`, drivers/char/random.c, Linux
    v6.18.46), so Linux discards bits 32-63 where this arm, comparing
    the whole word, declines.

    `buflen` IS BOUNDED BY `Uaccess.rw_bytes_max`, for the same reason and by
    the same mechanism as `read`'s and `write`'s `count`.  The
    destination check below is `read_bytes_map (in_wmem i) buf buflen`,
    which is `read_bytes_aux` over `word_to_nat buflen`, so this is a
    fifth site that builds the unary numeral described there — and it
    does so before it looks at a single byte of memory, so an
    unbounded `buflen` takes the extracted checker down exactly as an
    unbounded `write` did.  The bound costs nothing real: Linux clamps
    a getrandom request at INT_MAX, and no program has a reason to ask
    for 128 KiB of entropy in one call.  Decided after the flag check,
    which Linux also makes first. -/
def getrandom_spec (buf buflen flags : word) : SysSpec SyscallEffect :=
  if !(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK)) then unmodeled
  else
  if !modeled_rw_count buflen then unmodeled   -- see `Uaccess.rw_bytes_max`
  else
  bind inputSpec fun i =>
  match read_bytes_map i.in_wmem buf buflen with
  | none => unmodeled   -- unwritable destination buffer: program bug, fail closed
  | some _ =>
      let interrupted : SysSpec SyscallEffect :=
        bind (errno_from getrandom_errnos) (fun e => err_ret e)
      if !w_is0 buflen
      then
        if decide ((buflen.toNat : Int) ≤ getrandom_small_max)
        then
          -- THE SMALL REQUEST: full delivery, and nothing else — see
          -- `getrandom_small_max`.  The bytes are still the
          -- environment's; only their number is fixed.
          bind (choose (fun bs : List byte => (bs.length : Int) = (buflen.toNat : Int)))
            (fun bs => pure (mkEffect (len_word bs) [(buf, bs)] []))
        else
          alt interrupted
            (bind (choose (fun bs : List byte =>
                     (1 : Int) ≤ (bs.length : Int) ∧
                     (bs.length : Int) ≤ (buflen.toNat : Int)))
              (fun bs => pure (mkEffect (len_word bs) [(buf, bs)] [])))
      else
        -- A ZERO-BYTE REQUEST moves nothing, so `import_ubuf`'s (lib/iov_iter.c at v6.18.46)
        -- `access_ok` on the range is the whole of what is left to
        -- decide — the same test `read` and `write` face, spelled out
        -- here rather than through `Uaccess.access_ok_zero` because the
        -- interrupted alternative has to survive into the -EFAULT arm.
        -- (Linux can be interrupted in `wait_for_random_bytes` BEFORE
        -- it imports the buffer, so -EINTR is admissible whatever the
        -- range verdict.)
        if access_okb buf (buflen.toNat : Int)
        then alt interrupted (ret_only (BitVec.ofInt 64 0))
        else alt interrupted (err_ret EFAULT)

/-! ## Sanity checks

  There is no closed computation to re-use — the file is three definitions
  and the spec — so these are port checks in the spirit of the ones in
  `Sys/Fs/Readdir.lean`: the flag gate (bad flags are DECLINED, not
  answered -EINVAL — fail closed, see the flags note), the delivered
  bytes shape, the zero-byte shape, the two errnos, and the count gate. -/

/-- `input` at the head of a chain binds the incoming input and steps
    nothing — `Monad.bind_getModel`'s counterpart for `Monad.input`.  A
    port helper (this file reuses no lemmas), used by the checks
    below to see past the spec's `i <- input`. -/
private theorem bind_inputSpec {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event) :
    bind inputSpec k i m o ↔ k i i m o := by
  cases o with
  | ok x m2 evs =>
      simp only [bind, inputSpec, input]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        simp only [Outcome.ok.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        simp at h3
        subst h3
        exact h2
      · intro h
        exact ⟨i, m, [], evs, rfl, h, rfl⟩
  | unmodeled =>
      simp only [bind, inputSpec, input]
      constructor
      · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
        · exact absurd h (by simp)
        · simp only [Outcome.ok.injEq] at h1
          obtain ⟨rfl, rfl, rfl⟩ := h1
          exact h2
      · intro h
        exact Or.inr ⟨i, m, [], rfl, h⟩

/-- The injectable set is one errno wide, and it is `EINTR`. -/
example : getrandom_errnos = [EINTR] := rfl

/-- -EINTR's encoding, `-4` in two's complement. -/
example : (getrandom_errnos.map errno_ret) = [BitVec.ofInt 64 (-4)] := by decide

/-- The small-request bound is the 256 of getrandom(2)'s documented
    guarantee, not a page. -/
example : getrandom_small_max = 256 := rfl

/-- The two flag bits the spec names are the uapi ones. -/
example : GRND_NONBLOCK = 1 := rfl

example : GRND_RANDOM = 2 := rfl

/-- A syscall input for `getrandom` (278) whose destination range is
    fully writable: every address holds a byte. -/
private def demoInput : SyscallInput :=
  { in_sysno := 278, in_args := [0x100, 8, 0], in_mem := fun _ => some 0,
    in_wmem := fun _ => some 0 }

/-- The same input with NO writable memory at all: the destination check
    is the one that has to decline. -/
private def demoInputNone : SyscallInput :=
  { in_sysno := 278, in_args := [0x100, 8, 0], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- The model the checks run in: empty fd table, empty VM ledger, EOF on
    stdin, empty file system, no halt and no rlimit.  `getrandom_spec`
    reads the model not at all (it reads the INPUT and the environment),
    so any model serves. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The destination walk the checks below rewrite through: at `demoInput`
    every address in a range holds a byte, so a range is always
    `some`-shaped and only the flag/count/shape gates decide. -/
private theorem demo_read_0 :
    read_bytes_map demoInput.in_wmem (256#64) (0#64) = some [] := by decide

private theorem demo_read_4 :
    read_bytes_map demoInput.in_wmem (256#64) (4#64) = some [0, 0, 0, 0] := by decide

/-- The 300 bytes a 300-byte all-mapped range holds.  A `def` rather than
    a literal so the rewrite below does not send `simp` through
    `List.replicate` on every pass. -/
private def demoBytes300 : List byte := List.replicate 300 0

set_option maxRecDepth 100000 in
private theorem demo_read_300 :
    read_bytes_map demoInput.in_wmem (256#64) (300#64) = some demoBytes300 := by
  decide

private theorem demo_read_none :
    read_bytes_map demoInputNone.in_wmem (256#64) (8#64) = none := by decide

/-- `GRND_RANDOM` — the blocking /dev/random pool — is DECLINED, not
    answered: the spec covers the initialized urandom pool only, and a
    return invented here would be a behavior the model cannot back. -/
example : getrandom_spec 0x100 8 (2 : word) demoInput demoModel .unmodeled := by
  simp [getrandom_spec, GRND_NONBLOCK, unmodeled]

/-- …and it is not -EINVAL either: fail-closed means `unmodeled`, so no
    negative-errno return is admissible for this call. -/
example :
    ¬ getrandom_spec 0x100 8 (2 : word) demoInput demoModel
        (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp [getrandom_spec, GRND_NONBLOCK, unmodeled]

/-- An unknown flag bit (`8`) is declined the same way. -/
example : getrandom_spec 0x100 8 (8 : word) demoInput demoModel .unmodeled := by
  simp [getrandom_spec, GRND_NONBLOCK, unmodeled]

/-- …and so is a SET HIGH HALF: the kernel would discard bits 32-63 (its
    `flags` is `unsigned int`) where this arm, comparing the whole word,
    declines — the narrowing the flags note records. -/
example :
    getrandom_spec 0x100 8 (BitVec.ofInt 64 4294967297) demoInput demoModel
      .unmodeled := by
  simp [getrandom_spec, GRND_NONBLOCK, unmodeled]

/-- A request above `Uaccess.rw_bytes_max` is declined: the model will not
    build a 128 KiB-sized numeral on the checker's behalf. -/
example : getrandom_spec 0x100 131073 (1 : word) demoInput demoModel .unmodeled := by
  simp [getrandom_spec, GRND_NONBLOCK, modeled_rw_count, rw_bytes_max, unmodeled]

/-- `GRND_NONBLOCK` is accepted, and is treated EXACTLY like 0: on a
    modern kernel the pool is ready long before user code runs, so the
    flag never changes a urandom read's outcome.  This is the claim the
    flags note makes, checked as spec equivalence. -/
example (buf buflen : word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    getrandom_spec buf buflen (0 : word) i m o ↔
      getrandom_spec buf buflen (1 : word) i m o := by
  simp [getrandom_spec, GRND_NONBLOCK]

/-- A ZERO-BYTE REQUEST succeeds with 0 and moves no byte — the canonical
    zero-byte shape: `mkEffect 0 [] []`, i.e. no `(buf, [])` entry. -/
example :
    getrandom_spec 0x100 0 (0 : word) demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp [getrandom_spec, GRND_NONBLOCK, demo_read_0, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, access_okb, TASK_SIZE]
  simp [alt, ret_only, pure]

/-- …AND -EINTR SURVIVES INTO THE ZERO-BYTE ARM: Linux can be interrupted
    in `wait_for_random_bytes` before it ever imports the buffer, so the
    interrupted alternative is not narrowed away.  The witness is the one
    element of `getrandom_errnos`. -/
example :
    getrandom_spec 0x100 0 (0 : word) demoInput demoModel
      (.ok (mkEffect (errno_ret EINTR) [] []) demoModel []) := by
  simp [getrandom_spec, GRND_NONBLOCK, demo_read_0, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, access_okb, TASK_SIZE]
  simp [alt, err_ret, ret_only, errno_from, choose, bind, pure]
  exact Or.inl ⟨EINTR, by decide, rfl⟩

/-- A zero-byte request at a range `access_ok` refuses is -EFAULT — still
    beside the interrupted alternative. -/
example :
    getrandom_spec 0x800000000001 0 (0 : word) demoInput demoModel
      (.ok (mkEffect (errno_ret EFAULT) [] []) demoModel []) := by
  have hread : read_bytes_map demoInput.in_wmem (0x800000000001#64) (0#64) =
      some [] := by decide
  simp [getrandom_spec, GRND_NONBLOCK, hread, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, access_okb, TASK_SIZE]
  simp [alt, err_ret, ret_only, errno_from, choose, bind, pure]

/-- THE DELIVERED-BYTES SHAPE (small request): a request of 4 bytes is
    delivered IN FULL — one write entry at `buf`, exactly 4 bytes, and
    the return word is those 4 bytes (`len_word`).  Which 4 bytes is the
    environment's choice, not the spec's. -/
example :
    getrandom_spec 0x100 4 (0 : word) demoInput demoModel
      (.ok (mkEffect (len_word ([1, 2, 3, 4] : List byte))
          [(0x100, ([1, 2, 3, 4] : List byte))] []) demoModel []) := by
  simp [getrandom_spec, GRND_NONBLOCK, demo_read_4, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, getrandom_small_max]
  simp [choose, bind, pure]

/-- …and the write entry is the canonical delivery shape
    `Uaccess.delivered_writes` names, which omits an empty delivery. -/
example : delivered_writes 0x100 [1, 2, 3, 4] = [(0x100, [1, 2, 3, 4])] := by decide

example : delivered_writes 0x100 ([] : List byte) = [] := by decide

/-- A LARGE REQUEST (above the small bound) may be cut short by a signal:
    the delivered count is environment-chosen in `[1, buflen]`, so a
    one-byte delivery is admissible. -/
example :
    getrandom_spec 0x100 300 (0 : word) demoInput demoModel
      (.ok (mkEffect (len_word ([7] : List byte)) [(0x100, ([7] : List byte))] [])
        demoModel []) := by
  simp [getrandom_spec, GRND_NONBLOCK, demo_read_300, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, getrandom_small_max]
  simp [alt, err_ret, ret_only, errno_from, choose, bind, pure]

/-- …and so is -EINTR for the same call. -/
example :
    getrandom_spec 0x100 300 (0 : word) demoInput demoModel
      (.ok (mkEffect (errno_ret EINTR) [] []) demoModel []) := by
  simp [getrandom_spec, GRND_NONBLOCK, demo_read_300, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, getrandom_small_max]
  simp [alt, err_ret, ret_only, errno_from, choose, bind, pure]
  exact ⟨EINTR, by decide, rfl⟩

/-- An UNWRITABLE destination range is `unmodeled` (fail closed): the spec
    declines rather than inventing either a delivery or an -EFAULT. -/
example :
    getrandom_spec 0x100 8 (0 : word) demoInputNone demoModel .unmodeled := by
  simp [getrandom_spec, GRND_NONBLOCK, demo_read_none, bind_inputSpec, w_is0, bv_eqb,
    modeled_rw_count, rw_bytes_max, unmodeled]

/-- The errnos the spec can hand back really are the kernel's numbers in
    the return word. -/
example : errno_ret EINTR = BitVec.ofInt 64 (-4) := by decide

example : errno_ret EFAULT = BitVec.ofInt 64 (-14) := by decide

end LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random
