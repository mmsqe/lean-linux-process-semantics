/-
  * LinuxProcessSem.State — the model state

  CHUNK 0. The errno constants, the `SyscallInput`/`SyscallEffect` records, and the
  user-memory readers (`read_bytes_*` and `readable_bytes_*`) with their lemmas,
  through the proof of `readable_bytes_eq`. the remaining sections (starting with
  `readable_bytes_length_le` at lines 1011–1018, then `path_max`, the pathname/iovec
  readers, the `Model` record and its accessors, and the `model` rewrite matrix) are
  appended to this file by later chunks. The line range is cited here so every chunk
  can be checked against the same region of the source.

  TRUST BOUNDARY: this file is part of the trusted specification.

  The chunk count is computed as
  `Z.to_nat (bv_unsigned len / wmem_chunk)` over `Z`; here `wmem_chunk`
  is a `Nat` and the same division is plain `Nat` division on
  `word_to_nat len`.  `bv_unsigned len` is non-negative and the divisor
  is the literal 4096, so the two agree exactly, and the proofs stay in
  `Nat` (`Nat.div_add_mod`).
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/-! ## Errno values -/

/-- Errno values the model returns deterministically. -/
def EPERM  : Int := 1
def ENOENT : Int := 2
def ESRCH  : Int := 3
def EBADF  : Int := 9
def ECHILD : Int := 10
def EFAULT : Int := 14
def EEXIST : Int := 17
def ENOTDIR : Int := 20
def EISDIR : Int := 21
def EINVAL : Int := 22
def ENOTTY : Int := 25
def ESPIPE : Int := 29
def EPIPE  : Int := 32
def ERANGE : Int := 34
def ENAMETOOLONG : Int := 36
def ENOTEMPTY : Int := 39

/-- Errno values the per-syscall failure-injection sets draw from
    (see `Syscall.errno_from` and the `*_errnos` lists).  `EINVAL` above is
    NOT among them: every syscall that can return it does so
    deterministically, from arguments the model reads.

    WHICH BLOCK A VALUE SITS IN IS PROSE, NOT A FACT ANYTHING READS.  The
    split records how the modeled surface uses each errno today, and it
    stops being true the moment a syscall uses one the other way.  Three
    values already break it: `EPERM`, which the credential specs return
    deterministically while `Namei.unlinkat_errnos` also draws it as an
    alternative, and `ENOENT` and `ENAMETOOLONG`, which several specs return
    deterministically while `DPath.getcwd_errnos` draws both — a value
    can be both, and the split cannot say so.  `Kernel.Sys.setsid_spec` is a
    THIRD shape the split has no room for: it offers `EPERM` as one arm of
    an `alt` until a setsid has succeeded and returns it deterministically
    after, so the same value is alternative and deterministic in the same
    spec, decided by state rather than by arguments — and it is drawn from
    no `*_errnos` list at all.  Nothing depends on the
    placement; the load-bearing facts are the VALUE and the `*_errnos`
    list that names it. -/
def EINTR  : Int := 4
def ENOMEM : Int := 12
def EACCES : Int := 13
def EBUSY  : Int := 16
def ENFILE : Int := 23
def EMFILE : Int := 24
def EROFS  : Int := 30

/-- Other errno values.

    Injected on exactly one shape: a credential setter that moves the REAL
    uid, where the kernel's `set_user` and `set_cred_ucounts` allocate and
    can fail (see `Kernel.Sys.setid_errnos`).  It is deliberately NOT in
    any other syscall's injection set — admitting a blocking-style EAGAIN
    where no kernel produces one would add nondeterminism a target could
    hide behavior in, and programs handle it inconsistently anyway. -/
def EAGAIN : Int := 11

/-- Socket errno values.  All from the asm-generic table
    (include/uapi/asm-generic/errno.h and errno-base.h, v6.12), which
    riscv64 uses unchanged — arch/riscv has no errno.h of its own, and
    include/uapi/asm-generic/Kbuild lists errno.h as mandatory-y, so the
    generic header is the one that applies. -/
def ENOTSOCK        : Int := 88
def EMSGSIZE        : Int := 90
def ENOPROTOOPT     : Int := 92
def EPROTONOSUPPORT : Int := 93
def ESOCKTNOSUPPORT : Int := 94
def EOPNOTSUPP      : Int := 95
def EAFNOSUPPORT    : Int := 97
def EADDRINUSE      : Int := 98
def ECONNRESET      : Int := 104
def EISCONN         : Int := 106
def ENOTCONN        : Int := 107
def ETIMEDOUT       : Int := 110

/-- The one value in this block NO spec returns.  It names the canonical
    outcome of the connection attempt `Net.Socket.connect_spec` declines,
    and `Checks/Cases/Net/Socket.lean` pins that the declined arm answers
    `Unmodeled` to a real errno rather than to a bare 111:
    `connect_attempt_is_declined_not_refused` declines 0, -ECONNREFUSED
    and -ETIMEDOUT alike, so no errno is smuggled in on that arm. -/
def ECONNREFUSED    : Int := 111

/-! ## Syscall inputs and effects -/

/-- The syscall input: the number, the argument registers, and the two
    memory views the spec reads. -/
structure SyscallInput where
  mkInput ::
  /-- a7 at `ecall` -/
  in_sysno : word
  /-- a0..a5 at `ecall` (decoded register values) -/
  in_args : List word
  /-- pre-syscall memory: byte-level `addr -> option byte`, writable memory
      merged over ROM (exactly what the process can read); `none` = address
      not mapped.  Used for syscall SOURCE buffers (write data, openat
      paths), which may live in .rodata. -/
  in_mem : word → Option byte
  /-- the WRITABLE view: the writable overlay merged over writable ('w')
      segments only — exactly the addresses the kernel may write into
      (`RiscvSemantics.ms_writable_byte`).  Syscall OUTPUT buffers
      (read/getrandom destinations) must be fully defined here, the
      analogue of the kernel's copy_to_user EFAULT check; an output
      buffer that is unmapped or read-only is `unmodeled` (fail closed),
      except that `read` answers `-EFAULT` when not even the FIRST byte
      it would deliver can land, as the kernel does (see
      `ReadWrite.read_spec`). -/
  in_wmem : word → Option byte

/-- The `k`-th argument register value (0 when the list is shorter). -/
def in_arg (i : SyscallInput) (k : Nat) : word :=
  i.in_args.getD k (BitVec.ofInt 64 0)

/-- One symbolic memory copy.  Keeping the preserved prefix of a moved
    anonymous mapping as three words, rather than materializing its bytes,
    makes large `mremap` effects O(1). -/
structure MemCopy where
  mkCopy ::
  copy_src : word
  copy_dst : word
  copy_len : word

/-- What a syscall does to the machine: the a0 return value, the byte
    ranges it writes into user memory, the ranges it ZERO-FILLS
    (anonymous grants, mprotect exposure, and mremap growth), the ranges it
    UNMAPS (munmap, mremap, and PROT_NONE mappings), and the ranges it copies
    from a pre-effect snapshot.
    `Run.apply_effect` applies these deterministically; everything else
    (other GPRs, SP, PC, ROM, all other memory) is preserved by
    construction.

    `eff_zeros` ranges are (base, size) pairs — kept symbolic rather than
    materialized as byte lists so a multi-megabyte grant stays O(1) in
    the spec, the checker, and proofs.

    `eff_unmaps` is NOT expressible as a write: every covered byte
    becomes UNMAPPED (`none` in the writable overlay), so a later load
    from it faults — as a real munmapped page does — instead of reading
    stale bytes.  munmap, mremap, every successful PROT_NONE mmap, and a
    brk SHRINK (the freed page-aligned heap tail) emit it;
    `Run.apply_effect` erases the
    ranges before zeros and writes are applied.

    `eff_copies` snapshots its sources from the PRE-EFFECT memory.  This is
    essential for a moved `mremap`: the old range is unmapped by the same
    effect, but its preserved prefix must still be installed at the new
    address.  `Run.apply_effect` applies unmaps, then zeros, then these
    snapshot copies, then ordinary writes.

    `eff_copyins` records ranges that the syscall already read from user
    memory while selecting this outcome.  It is outcome data because the same
    errno can be returned either before or after a copy_from_user. -/
structure SyscallEffect where
  mkEffectU ::
  eff_ret    : word
  /-- (base address, bytes), applied in order -/
  eff_writes : List (word × List byte)
  /-- (base address, size) zero-filled ranges -/
  eff_zeros  : List (word × word)
  /-- (base address, size) unmapped ranges -/
  eff_unmaps : List (word × word)
  /-- pre-effect (source, destination, size) copies -/
  eff_copies : List MemCopy
  /-- ranges already read from user memory -/
  eff_copyins : List (word × Nat)

/-- The common no-unmap/no-copy/no-copyin domain convenience. -/
abbrev mkEffect (r : word) (ws : List (word × List byte)) (zs : List (word × word)) :
    SyscallEffect :=
  ⟨r, ws, zs, [], [], []⟩

/-- The same effect, with the ranges already read from user memory
    recorded (see the `eff_copyins` note on `SyscallEffect`). -/
def with_copyins (reads : List (word × Nat)) (eff : SyscallEffect) : SyscallEffect :=
  ⟨eff.eff_ret, eff.eff_writes, eff.eff_zeros, eff.eff_unmaps, eff.eff_copies, reads⟩

/-! ## Reading user memory (buffers and NUL-terminated strings) -/

/-- Read `len` consecutive bytes starting at `a`, or `none` if any byte in
    the range is unmapped.  Addresses advance with wrapping `bv` addition
    (a buffer straddling the top of the
    address space is not something a real process can hand the kernel). -/
def read_bytes_aux (mp : word → Option byte) (a : word) : Nat → Option (List byte)
  | 0 => some []
  | k + 1 =>
      match mp a with
      | none => none
      | some b =>
          match read_bytes_aux mp (a + 1) k with
          | some r => some (b :: r)
          | none => none

/-- `read_bytes_aux` is the shape proofs use, and NOT what the checker
    may execute on a long range: the recursion rebuilds its list on the
    way OUT, one stack frame per byte, and the extracted checker dies of
    that between 2^17 and 2^18 frames on an OCaml 4 runtime, and pays
    for it in quadratic TIME rather than dying on the OCaml 5 the opam
    file requires — which
    the read count window
    makes reachable, since a delivered prefix may be
    `MAX_RW_COUNT` long.  `read_bytes_map` therefore EXECUTES as a
    chunked accumulator loop: `read_bytes_acc` extends its accumulator
    with the walked bytes REVERSED and returns through a tail call, the
    chunk loop hands the fuel out `wmem_chunk` bytes at a time so no
    unary numeral scales with the length either (the depth a Peano
    conversion survives is a property of the OCaml runtime
    configuration, which nothing here fixes),
    and one `rev_append` at the end restores byte order.
    `read_bytes_map_eq` is the equation every proof goes through;
    nothing outside this block unfolds `read_bytes_map`'s body. -/
def wmem_chunk : Nat := 4096

/-- The accumulator loop `read_bytes_map` executes: the walked bytes land
    in `acc` REVERSED, and the result comes back through a tail call. -/
def read_bytes_acc (mp : word → Option byte) (a : word) : Nat → List byte → Option (List byte)
  | 0, acc => some acc
  | k + 1, acc =>
      match mp a with
      | none => none
      | some b => read_bytes_acc mp (a + 1) k (b :: acc)

/-- Walk `q` chunks of `k` bytes each, threading the accumulator. -/
def read_bytes_chunks (mp : word → Option byte) (a : word) :
    Nat → Nat → List byte → Option (List byte)
  | 0, _k, acc => some acc
  | q + 1, k, acc =>
      match read_bytes_acc mp a k acc with
      | none => none
      | some acc' => read_bytes_chunks mp (a + nat_to_word k) q k acc'

/-- `rev_append l acc` is `l.reverse ++ acc`.  It is used here with
    `acc = []`, where it restores the byte order the accumulator loops
    reversed.

  this is literally `l.reverse ++ acc`, and `List.reverse` is
    the tail-recursive worker, so the cost profile the comments above
    describe is preserved. -/
def rev_append {α : Type} (l acc : List α) : List α := l.reverse ++ acc

/-- Read `len` bytes starting at `a`. -/
def read_bytes_map (mp : word → Option byte) (a len : word) : Option (List byte) :=
  let n := word_to_nat len
  match read_bytes_chunks mp a (n / wmem_chunk) wmem_chunk [] with
  | none => none
  | some acc =>
      match read_bytes_acc mp (a + nat_to_word (n / wmem_chunk * wmem_chunk))
              (n % wmem_chunk) acc with
      | none => none
      | some acc' => some (rev_append acc' [])

theorem read_bytes_acc_aux (mp : word → Option byte) (k : Nat) (a : word) (acc : List byte) :
    read_bytes_acc mp a k acc
      = match read_bytes_aux mp a k with
        | none => none
        | some w => some (rev_append w acc) := by
  induction k generalizing a acc with
  | zero => rfl
  | succ k ih =>
    cases h : mp a with
    | none => simp [read_bytes_acc, read_bytes_aux, h]
    | some b =>
      simp only [read_bytes_acc, read_bytes_aux, h]
      rw [ih]
      cases h2 : read_bytes_aux mp (a + 1) k with
      | none => simp
      | some w => simp [rev_append, List.reverse_cons, List.append_assoc]

theorem read_bytes_aux_split (mp : word → Option byte) (j : Nat) :
    ∀ (k : Nat) (a : word),
      read_bytes_aux mp a (j + k)
        = match read_bytes_aux mp a j with
          | none => none
          | some w1 =>
              match read_bytes_aux mp (a + nat_to_word j) k with
              | none => none
              | some w2 => some (w1 ++ w2) := by
  induction j with
  | zero =>
    intro k a
    have h0 : a + nat_to_word 0 = a := by simp [nat_to_word]
    simp only [Nat.zero_add, read_bytes_aux, h0]
    cases read_bytes_aux mp a k <;> rfl
  | succ j ih =>
    intro k a
    rw [Nat.succ_add]
    cases h : mp a with
    | none => simp [read_bytes_aux, h]
    | some b =>
      simp only [read_bytes_aux, h]
      rw [ih]
      have hstep : a + 1 + nat_to_word j = a + nat_to_word (j + 1) := by
        unfold nat_to_word
        bv_omega
      rw [hstep]
      cases h1 : read_bytes_aux mp (a + 1) j with
      | none => simp
      | some w1 =>
        cases h2 : read_bytes_aux mp (a + nat_to_word (j + 1)) k with
        | none => simp
        | some w2 => simp

theorem rev_append_app {α : Type} (l1 l2 acc : List α) :
    rev_append (l1 ++ l2) acc = rev_append l2 (rev_append l1 acc) := by
  simp [rev_append, List.reverse_append, List.append_assoc]

theorem read_bytes_chunks_flat (mp : word → Option byte) (q : Nat) :
    ∀ (k : Nat) (a : word) (acc : List byte),
      read_bytes_chunks mp a q k acc
        = match read_bytes_aux mp a (q * k) with
          | none => none
          | some w => some (rev_append w acc) := by
  induction q with
  | zero =>
    intro k a acc
    simp [read_bytes_chunks, read_bytes_aux, rev_append]
  | succ q ih =>
    intro k a acc
    have hmul : (q + 1) * k = k + q * k := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hmul]
    simp only [read_bytes_chunks]
    rw [read_bytes_acc_aux]
    rw [read_bytes_aux_split]
    cases h1 : read_bytes_aux mp a k with
    | none => simp
    | some w1 =>
      dsimp only
      rw [ih]
      cases h2 : read_bytes_aux mp (a + nat_to_word k) (q * k) with
      | none => simp
      | some w2 =>
        dsimp only
        simp [rev_append_app]

theorem read_bytes_map_eq (mp : word → Option byte) (a len : word) :
    read_bytes_map mp a len = read_bytes_aux mp a (word_to_nat len) := by
  unfold read_bytes_map
  dsimp only
  rw [read_bytes_chunks_flat]
  have hdiv : word_to_nat len
      = word_to_nat len / wmem_chunk * wmem_chunk + word_to_nat len % wmem_chunk := by
    unfold wmem_chunk
    omega
  conv => rhs; rw [hdiv]
  rw [read_bytes_aux_split]
  cases h1 : read_bytes_aux mp a (word_to_nat len / wmem_chunk * wmem_chunk) with
  | none => simp
  | some w1 =>
    dsimp only
    rw [read_bytes_acc_aux]
    cases h2 : read_bytes_aux mp
        (a + nat_to_word (word_to_nat len / wmem_chunk * wmem_chunk))
        (word_to_nat len % wmem_chunk) with
    | none => simp
    | some w2 =>
      dsimp only
      simp [rev_append, List.reverse_append, List.reverse_reverse]

/-! ## The longest readable prefix -/

/-- The longest READABLE PREFIX of `[a, a+len)`: the consecutive mapped
    bytes starting at `a`, stopping at the first unmapped byte (or at
    `len`).  This is what a real kernel's copy_from_user can move before
    faulting — see `ReadWrite.write_spec`'s short-write semantics.

    `readable_bytes_aux` is the shape proofs use, and — exactly as with
    `read_bytes_aux` above — NOT what the checker may execute on a long
    range: it rebuilds its list on the way OUT, one stack frame per byte,
    and it converts `len` to a unary numeral before the first memory
    lookup.  Both costs scale with the COUNT a `write` names, and the
    write direction does not bound that count by `Uaccess.rw_bytes_max`;
    the execution shape below is what makes that safe. -/
def readable_bytes_aux (mp : word → Option byte) (a : word) : Nat → List byte
  | 0 => []
  | k + 1 =>
      match mp a with
      | none => []
      | some b => b :: readable_bytes_aux mp (a + 1) k

theorem readable_bytes_aux_length_le (mp : word → Option byte) (k : Nat) (a : word) :
    (readable_bytes_aux mp a k).length ≤ k := by
  induction k generalizing a with
  | zero => simp [readable_bytes_aux]
  | succ k ih =>
    cases h : mp a with
    | none => simp [readable_bytes_aux, h]
    | some b =>
      have := ih (a + 1)
      simp only [readable_bytes_aux, h, List.length_cons]
      omega

/-- `readable_bytes` EXECUTES as the chunked accumulator loop
    `read_bytes_map` carries, with one extra thing to carry: this walk
    may STOP EARLY, so the accumulator pair reports whether the `k` bytes
    it was given were all mapped.  `false` is what ends the chunk loop —
    the prefix is complete at that point and no later chunk can extend
    it.  The `k`-byte inner walk is where the stack depth is spent, and
    it is `wmem_chunk`, not `len`; the only unary numeral that scales
    with `len` is the chunk COUNT, which is `wmem_chunk` times smaller.
    One `rev_append` at the end restores byte order.

    `readable_bytes_eq` is the equation every proof goes through; nothing
    outside this block unfolds `readable_bytes`'s body. -/
def readable_bytes_acc (mp : word → Option byte) (a : word) : Nat → List byte → Bool × List byte
  | 0, acc => (true, acc)
  | k + 1, acc =>
      match mp a with
      | none => (false, acc)
      | some b => readable_bytes_acc mp (a + 1) k (b :: acc)

/-- Walk `q` chunks of `k` bytes each, threading the accumulator and the
    all-mapped flag; `false` ends the loop. -/
def readable_bytes_chunks (mp : word → Option byte) (a : word) :
    Nat → Nat → List byte → Bool × List byte
  | 0, _k, acc => (true, acc)
  | q + 1, k, acc =>
      match readable_bytes_acc mp a k acc with
      | (false, acc') => (false, acc')
      | (true, acc') => readable_bytes_chunks mp (a + nat_to_word k) q k acc'

/-- The longest readable prefix of `[a, a+len)`. -/
def readable_bytes (mp : word → Option byte) (a len : word) : List byte :=
  let n := word_to_nat len
  match readable_bytes_chunks mp a (n / wmem_chunk) wmem_chunk [] with
  | (false, acc) => rev_append acc []
  | (true, acc) =>
      rev_append (readable_bytes_acc mp
                    (a + nat_to_word (n / wmem_chunk * wmem_chunk))
                    (n % wmem_chunk) acc).2 []

theorem readable_bytes_acc_flat (mp : word → Option byte) (k : Nat) (a : word) (acc : List byte) :
    readable_bytes_acc mp a k acc
      = ((readable_bytes_aux mp a k).length == k,
         rev_append (readable_bytes_aux mp a k) acc) := by
  induction k generalizing a acc with
  | zero => simp [readable_bytes_acc, readable_bytes_aux, rev_append]
  | succ k ih =>
    cases h : mp a with
    | none => simp [readable_bytes_acc, readable_bytes_aux, h, rev_append]
    | some b =>
      simp only [readable_bytes_acc, readable_bytes_aux, h, List.length_cons]
      rw [ih]
      simp [rev_append, List.reverse_cons, List.append_assoc]

/-- Splitting the walk at `j`: the second part is reached exactly when the
    first ran to its full length — one unmapped byte in the first `j`
    ends the whole prefix. -/
theorem readable_bytes_aux_split (mp : word → Option byte) (j : Nat) :
    ∀ (k : Nat) (a : word),
      readable_bytes_aux mp a (j + k)
        = if (readable_bytes_aux mp a j).length == j
          then readable_bytes_aux mp a j ++ readable_bytes_aux mp (a + nat_to_word j) k
          else readable_bytes_aux mp a j := by
  induction j with
  | zero =>
    intro k a
    have h0 : a + nat_to_word 0 = a := by simp [nat_to_word]
    simp [readable_bytes_aux, h0]
  | succ j ih =>
    intro k a
    rw [Nat.succ_add]
    cases h : mp a with
    | none => simp [readable_bytes_aux, h]
    | some b =>
      simp only [readable_bytes_aux, h, List.length_cons]
      rw [ih]
      have hstep : a + 1 + nat_to_word j = a + nat_to_word (j + 1) := by
        unfold nat_to_word
        bv_omega
      rw [hstep]
      by_cases h : (readable_bytes_aux mp (a + 1) j).length = j
      · have h1 : ((readable_bytes_aux mp (a + 1) j).length == j) = true :=
          beq_iff_eq.mpr h
        have h2 : ((readable_bytes_aux mp (a + 1) j).length + 1 == j + 1) = true :=
          beq_iff_eq.mpr (by rw [h])
        rw [ite_eq_left h1, ite_eq_left h2]
        simp
      · have h1 : ¬(((readable_bytes_aux mp (a + 1) j).length == j) = true) :=
          fun hc => h (beq_iff_eq.mp hc)
        have h2 : ¬(((readable_bytes_aux mp (a + 1) j).length + 1 == j + 1) = true) := by
          intro hc
          have hne : (readable_bytes_aux mp (a + 1) j).length + 1 ≠ j + 1 := by omega
          exact hne (beq_iff_eq.mp hc)
        rw [ite_eq_right h1, ite_eq_right h2]

theorem readable_bytes_chunks_flat (mp : word → Option byte) (q : Nat) :
    ∀ (k : Nat) (a : word) (acc : List byte),
      readable_bytes_chunks mp a q k acc
        = ((readable_bytes_aux mp a (q * k)).length == q * k,
           rev_append (readable_bytes_aux mp a (q * k)) acc) := by
  induction q with
  | zero =>
    intro k a acc
    simp [readable_bytes_chunks, readable_bytes_aux, rev_append]
  | succ q ih =>
    intro k a acc
    have hmul : (q + 1) * k = k + q * k := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hmul]
    simp only [readable_bytes_chunks]
    rw [readable_bytes_acc_flat]
    rw [readable_bytes_aux_split]
    cases hk : (readable_bytes_aux mp a k).length == k with
    | false =>
      -- the prefix stopped inside this chunk: no later chunk can extend it
      have hlen : (readable_bytes_aux mp a k).length ≤ k :=
        readable_bytes_aux_length_le mp k a
      have hne : (readable_bytes_aux mp a k).length ≠ k := by
        simpa [beq_eq_false_iff_ne] using hk
      have hlt : (readable_bytes_aux mp a k).length < k := by omega
      have hle : k ≤ k + q * k := Nat.le_add_right k (q * k)
      have hne' : (readable_bytes_aux mp a k).length ≠ k + q * k := by omega
      have hfalse : ((readable_bytes_aux mp a k).length == k + q * k) = false := by
        simpa [beq_eq_false_iff_ne] using hne'
      simp [hfalse]
    | true =>
      have hlenk : (readable_bytes_aux mp a k).length = k := by
        simpa [beq_iff_eq] using hk
      dsimp only
      rw [ih]
      rw [ite_eq_left rfl]
      rw [List.length_append, hlenk]
      rw [rev_append_app]
      by_cases h2 : (readable_bytes_aux mp (a + nat_to_word k) (q * k)).length = q * k
      · simp [h2]
      · have hb2 : ((readable_bytes_aux mp (a + nat_to_word k) (q * k)).length
            == q * k) = false := by
          simpa [beq_eq_false_iff_ne] using h2
        have h2' : k + (readable_bytes_aux mp (a + nat_to_word k) (q * k)).length
            ≠ k + q * k := by omega
        have hb2' : (k + (readable_bytes_aux mp (a + nat_to_word k) (q * k)).length
            == k + q * k) = false := by
          simpa [beq_eq_false_iff_ne] using h2'
        simp [hb2, hb2']

theorem readable_bytes_eq (mp : word → Option byte) (a len : word) :
    readable_bytes mp a len = readable_bytes_aux mp a (word_to_nat len) := by
  unfold readable_bytes
  dsimp only
  rw [readable_bytes_chunks_flat]
  have hdiv : word_to_nat len
      = word_to_nat len / wmem_chunk * wmem_chunk + word_to_nat len % wmem_chunk := by
    unfold wmem_chunk
    omega
  conv => rhs; rw [hdiv]
  rw [readable_bytes_aux_split]
  cases h1 : (readable_bytes_aux mp a
      (word_to_nat len / wmem_chunk * wmem_chunk)).length ==
      word_to_nat len / wmem_chunk * wmem_chunk with
  | false =>
    -- the prefix stopped inside the chunked part: the tail never runs
    dsimp only
    simp [rev_append, List.reverse_reverse]
  | true =>
    dsimp only
    rw [readable_bytes_acc_flat]
    dsimp only
    simp [rev_append, List.reverse_append, List.reverse_reverse]

/- =========================================================================
   CHUNK A1 — the type layer
   =========================================================================

   Appended after chunk 0 without touching it.  This is
   the chunk that makes `Sys Model SyscallInput event` real: every type
   `Monad.lean` and the syscall specs need from this file, and nothing else.

   Sections, in order: `VaSize` and its two task sizes (333–400),
   the standard-input stream (1760–1796), the network environment
   (2081–2462), the fd entry (2464–2621), `VmMaps` (2623–2713), the model
   subsystems (2859–2930), `Creds` (2932–2978), `ProcState` (3033–3334),
   `LimState` (3336–3378), `TimeState` (3380–3391), `Model` (3393–3437),
   and `event` (3896–3916).

   DELIBERATELY NOT HERE (each belongs to a later chunk and would be a
   function or a lemma rather than a type):
   - `creds_privileged` (3030–3031) — a `ProcState`-adjacent helper, B5;
   - `alloc_top` (2737) and its doc block (2715–2736) — B5;
   - `net_silent`, `nq_peer`, `nq_script`, `nq_rest` (2346–2366) — B4;
   - `stream_take` and the rest of the section (1797 onwards) — B3;
  - `stream_infinite` (1989–1991) — a coinductive Prop, not part of any
     type and part of B3; its Lean shape is recorded in;
   - the 25 `m_*` accessors (3439 onwards) — B5.

   DECIDABLE EQUALITY.  Derived only on records with no function field:
   `VaSize`, `NetStep`, `PeerAddr`, `VmMaps`, `VmState`, `FsState`,
   `Creds`, `LimState`, `TimeState`, `event`.  NOT on `SockState`,
   `FdEntry`, `FdState`, `IoState`, `ProcState` or `Model`: `NetStream` is
   a function (`Nat → NetStep`), so `FdEntry` (via `SockState`) and
   everything holding an `FdEntry` has no decidable equality — the same
  position a coinductive type is in: it gets no `EqDecision`.
   `PipeBuf` is an `abbrev` for a pair of core types, so it inherits the
   instances instead of deriving them.
-/

/-! ## The address-space size -/

/-- **The address-space size as a declared parameter of the run.**

    `TASK_SIZE` above, `sp_window_hi` and everything derived from them are
    the Sv48 kernel's numbers, and the paragraphs above them say so at
    length.  What they could not say is WHICH kernel a particular statement
    is about: the size is a boot-time fact of the machine a task runs on,
    not a property of the binary, and a proof made under one size says
    nothing about another.  So the size is a value the task DECLARES,
    carried in `ProcInput` as `in_va_size` and pinned by `Run.valid_input`
    and its per-size variants, the way the abort declaration is; a
    statement's quantifier then names the kernel it speaks about, and a
    reader does not have to know that "the model" means Sv48.

    The three values are the three page-table depths riscv64 Linux can boot
    with (`set_satp_mode`, arch/riscv/mm/init.c; the runtime globals
    `pgtable_l4_enabled` / `pgtable_l5_enabled` pick `PGDIR_SHIFT`,
    arch/riscv/include/asm/pgtable-64.h).  Two numbers follow from the
    depth and they do NOT move together, which is the reason the functions
    below are separate rather than one table:

    - `va_task_size` is `TASK_SIZE_64 = PGDIR_SIZE * PTRS_PER_PGD / 2`
      (arch/riscv/include/asm/pgtable.h, `TASK_SIZE_64`): 2^38, 2^47 or
      2^56.  It is the limit `access_ok` and `munmap` compare against.
    - `va_stack_top` is `STACK_TOP = DEFAULT_MAP_WINDOW = 1 <<
      (MMAP_VA_BITS - 1)` (arch/riscv/include/asm/processor.h), and
      `MMAP_VA_BITS_64` is `VA_BITS` CAPPED AT 48
      (arch/riscv/include/asm/pgtable.h, `MMAP_VA_BITS_64`), so it is
      2^38 under Sv39 and 2^47 under BOTH Sv48 and Sv57: an Sv57 kernel
      places its stacks and its top-down mmap base exactly where an Sv48
      one does, and differs only in how far up a program may reach.
      All at Linux v6.18.46, commit 1f99e9ab748f.

    The window and the mmap band are derived from `va_stack_top` by the
    same arguments the Sv48 constants above spell out: the window is the
    top and 2 GiB below it, the cap is the top less `MIN_GAP`.  The floor
    of the band is the one place a derivation does not carry over.  Under
    Sv39, `STACK_TOP - MAX_GAP` is under 2^36 while `arch_mmap_rnd` can
    subtract up to `(2^24 - 1)` pages, so `mmap_base`'s own subtraction
    (mm/util.c, `mmap_base`) goes below zero and wraps in the kernel's
    unsigned arithmetic; no positive floor holds of every rlimit and
    every draw, and the Sv39 instance admits any page-aligned base up to
    its cap rather than a floor that would exclude a real one.  The
    floor is read by no arm (`mmap_base_min`'s note), so this costs
    nothing but honesty.

    WHAT THE DECLARATION BUYS TODAY, stated here so nobody reads more
    into it: the spec arms below still compare against `TASK_SIZE`, the
    Sv48 constant, because that number is read at hundreds of sites
    through `access_okb` and the range tests, and the declared
    size is not threaded through them.  So the
    statements sealed under either other size are REFUSED rather than
    answered with the wrong limit: `Equivalence.strong_equiv_va` holds
    only of an `Sv48` input, and `Run.run` itself is the Sv48 run
    whatever the input declares -- which is why every obligation must
    be stated through the sealed families and not over `Run.run`
    directly.  The entry-state predicates (`Run.valid_sp_va` and its
    siblings) do read the declared size, so the window a statement
    quantifies over is the right one for its kernel even where the
    statement is refused. -/
inductive VaSize where
  | Sv39
  | Sv48
  | Sv57
  deriving DecidableEq, Repr

/-- The two numbers that are not already named above, as literal
    constants: 2^38 is both
    `TASK_SIZE_64` and `STACK_TOP` under Sv39, 2^56 is `TASK_SIZE_64`
    under Sv57. -/
def sv39_task_size : Int := 0x4000000000
def sv57_task_size : Int := 0x100000000000000

/- =========================================================================
   Standard input: an explicit INPUT of the semantics
   ========================================================================= -/

/-- The bytes the process will read from standard input, supplied UP
    FRONT as a parameter of the run (`Run.run`'s `stdin0` argument,
    universally quantified in `Equivalence.strong_universal_T` exactly
    like argv, envp and the initial file system).  A program's behavior
    is therefore a FUNCTION of its input rather than of an internal
    nondeterministic choice: the environment does not invent bytes (or
    an EOF position) mid-run.

    The type is a COLIST — a coinductive stream that may also STOP:

    - `ICons b s` — the next byte is `b`, and `s` is what follows;
    - `IEof`      — the input ends here.

    Being coinductive, it covers INFINITE inputs (a never-ending pipe,
    `yes` into the program); the `IEof` constructor is what lets it also
    express a finite input, which a plain `Stream byte` cannot.

    EOF IS STICKY BY CONSTRUCTION: `IEof` has no successor, so once a
    read observes it there is nothing left to deliver and every later
    read observes `IEof` again.  Stickiness is not a model
    invariant that a spec could accidentally break; it is a property of the
    representation.

    No validity predicate is needed: the elements are `byte = BitVec 8`, so
    "every byte really is a byte" holds by typing.

    Only channel 0 (stdin) is readable in this model — stdout/stderr are
    write-only (`FdEntry`) — so one stream suffices; there is no
    per-channel indexing.

  Lean 4 has no coinductive types and no corecursive definitions without
  `partial`/`unsafe`, both banned by `AGENTS.md`, so the stream is encoded as a TOTAL
  FUNCTION over its index: `s n = some b` means byte `n` is `b`, and `s n = none`
  means the stream ended at or before `n`. `IEof` is then the constant `none` stream
  and `ICons b s` is the stream that answers `b` at 0 and defers to `s` above it.
  Stickiness of EOF survives the encoding: every read past an end still sees `none`,
  and no corecursion is needed anywhere. The cost is that consumers pattern-match on
  `s 0` rather than on `s` (B3's `stream_take` is where that shows); -/
abbrev InputStream : Type := Nat → Option byte

/-- `IEof`: the input ends here (nullary EOF constructor). -/
def IEof : InputStream := fun _ => none

/-- `ICons b s`: the next byte is `b`, and `s` is what follows. -/
def ICons (b : byte) (s : InputStream) : InputStream
  | 0 => some b
  | n + 1 => s n

/- =========================================================================
   The network environment: what a hostile peer may do
   ========================================================================= -/

/-- One step of one connection's script: the four things a TCP peer on an
    established connection can do that the reading side can tell apart. -/
inductive NetStep where
  | fin
  | rst
  | timedOut
  | cons (b : byte)
  deriving DecidableEq, Repr

/-- **ONE CONNECTION'S SCRIPT, from the local program's point of view.**

    A TCP peer on an established connection can do exactly four things
    that the reading side can tell apart, and this type has one
    constructor for each.  Every kernel citation here is v6.12:

    - `NCons b rest` — it sent the byte `b`, and then went on to `rest`;
    - `NFin`         — it closed its sending half (FIN).  A read
                       delivers 0 (net/ipv4/tcp_input.c `tcp_fin` sets
                       RCV_SHUTDOWN and SOCK_DONE), and every later read
                       delivers 0 again;
    - `NRst`         — it reset the connection (RST).  ONE read answers
                       -ECONNRESET and every later read delivers 0;
    - `NTimedOut`    — it stopped acknowledging until the retransmit
                       timer gave up (net/ipv4/tcp_timer.c `tcp_write_err`).
                       ONE read answers -ETIMEDOUT, then 0.

    COINDUCTIVE, so a peer that never stops sending is expressible —
    the same reason `InputStream` is coinductive.

    THE TERMINALS ARE NULLARY ON PURPOSE.  A peer cannot send anything
    after a FIN or a RST, so "nothing follows a terminal" is a property
    of the REPRESENTATION rather than an invariant a spec could break —
    the house rule `InputStream` states for `IEof`.  It also means
    validity holds BY TYPING: the payload of `NCons` is a `byte`, the
    terminals carry nothing, so there is no `valid_net` side condition
    for `Run.valid_input` to carry.

    WHY EXACTLY {RST, TIMEDOUT} AND NOTHING ELSE.  Those are the only
    two errnos a peer can force on the read side of an established
    AF_INET/SOCK_STREAM socket with default options and no cooperation
    from the local program.  -EAGAIN needs O_NONBLOCK, -EINTR needs a
    signal, `-EHOSTUNREACH`/`-ENETUNREACH` need IP_RECVERR, and none of the
    three is in the modeled surface — so admitting them would model
    something the model cannot reach.

    WHY ONE ERROR AND THEN END-OF-STREAM, rather than a sticky error.
    include/net/sock.h `sock_error` reads the pending error with an
    `xchg`, so it is consumed by the read that reports it; and the RST
    path's tcp_done sets `sk_shutdown = SHUTDOWN_MASK`.  The read after
    an -ECONNRESET therefore returns 0.  A sticky error would be a
    plausible answer Linux does not give.

  It is encoded here as `Nat → NetStep`: observation `n` of a stream is the `n`-th
  thing the peer does. `NFin`/`NRst`/`NTimedOut`/`NCons` are then ordinary
  definitions (below), not constructors, so every downstream name survives; only the
  pattern-match shape changes (B4's `net_take` matches on `s 0`). -/
abbrev NetStream : Type := Nat → NetStep

/-- `NFin`: the peer closed its sending half (FIN). -/
def NFin : NetStream := fun _ => NetStep.fin

/-- `NRst`: the peer reset the connection (RST). -/
def NRst : NetStream := fun _ => NetStep.rst

/-- `NTimedOut`: the peer's retransmit timer gave up. -/
def NTimedOut : NetStream := fun _ => NetStep.timedOut

/-- `NCons b rest`: the peer sent the byte `b`, then went on to `rest`. -/
def NCons (b : byte) (rest : NetStream) : NetStream
  | 0 => NetStep.cons b
  | n + 1 => rest n

/-- The address the peer's SYN carried: its IP source address and its
    TCP source port, both verbatim from the wire, both entirely the
    peer's choice.  Stored in NETWORK byte order, the order
    `struct sockaddr_in` holds them in and `inet_getname` copies them
    out in.

    NOTHING IN THIS MODEL READS IT YET.  `accept` with a non-NULL
    address argument is unmodeled here because `SyscallEffect` has no
    address export: the write `move_addr_to_user` performs cannot be
    expressed at all.  THAT is the blocker, and not the absence of a
    caller worth having — `getsockname` (204) and `getpeername` (205)
    are modeled, and decline their own address write over the same
    missing export.  So the peer address never reaches the guest
    and never reaches a trace.  It is carried anyway because it is a
    real degree of freedom of the environment — two connections that
    send identical bytes from different addresses are different
    connections on Linux — and because carrying it now keeps the shape
    of `ProcInput` stable when the call that reports it is modeled. -/
structure PeerAddr where
  mkPeer ::
  /-- sin_addr.s_addr, network order -/
  pa_addr : BitVec 32
  /-- sin_port, network order -/
  pa_port : BitVec 16
  deriving DecidableEq, Repr

/-- **THE CONNECTIONS THE ENVIRONMENT OFFERS, in the order `accept` hands
    them over.**

    INFINITE — there is no nil.  `accept` must be RECEPTIVE
    (`Checks.Progress.receptive`: every syscall has an admissible
    outcome in every state), and a blocking `accept` on an exhausted
    queue has no answer at all: not a success, not an errno, and
    `Unmodeled` would make every source that loops on `accept` fail
    `modeled` on the one input that runs the queue out.  Since the queue
    is universally quantified, some input always would.

    THAT IS AN UNDER-APPROXIMATION: it excludes the environment in which `accept` blocks
    forever.  A source that would hang on Linux instead accepts another
    connection here, so a hang is not a behavior the theorem can
    distinguish.

    Being unable to run out is a different problem from being unable to
    FAIL, and it is fixed differently: `Net.Socket.accept4_spec` carries a
    live errno branch under `alt`, so fd exhaustion and the environment
    failures the model does not decide still have an answer.

    This type is coinductive in shape. It is encoded as `Nat → (PeerAddr ×
    NetStream)` — observation `n` of the queue is the `n`-th connection `accept`
    would hand over — and `NConn` below builds one connection on top of a rest queue.
    -/
abbrev NetQueue : Type := Nat → (PeerAddr × NetStream)

/-- `NConn peer script rest`: the head connection's peer and script, then
    `rest`. -/
def NConn (peer : PeerAddr) (script : NetStream) (rest : NetQueue) : NetQueue
  | 0 => (peer, script)
  | n + 1 => rest n

/- =========================================================================
   Model state — threaded across the whole run
   ========================================================================= -/

/-- **THE LIFE OF A SOCKET, as much of it as this model covers.**

    Only AF_INET/SOCK_STREAM sockets ever enter the fd table:
    `Net.Socket.socket_spec` declines every other domain and type, so a
    `FdSocket` is always a TCP socket and the domain, type and protocol
    need not be stored.  (That is also why "listen on a UDP socket is
    -EOPNOTSUPP" never arises here: there are no UDP sockets.)

    - `SkFresh`      — created by `socket`, not yet bound.  `read` is
                       -ENOTCONN; `accept` and a second `bind` are
                       -EINVAL; `listen` succeeds, autobinding an
                       ephemeral port (net/ipv4/inet_connection_sock.c:
                       inet_csk_listen_start).
    - `SkBound`      — `bind` accepted.  The address is not stored
                       because the only bind the model accepts is
                       INADDR_ANY on port 0; every other address needs
                       port-table state a one-process model does not
                       have, and is declined rather than guessed.
    - `SkListening`  — `listen` accepted.  `accept` draws from the
                       environment's queue; `read` is -ENOTCONN.
    - `SkConnected peer chan rx` — handed over by `accept`.  `peer` is
                       the address the SYN carried, `chan` is the trace
                       channel this connection's bytes are reported on
                       (see `Net.Socket.conn_channel`), and `rx` is what the
                       peer has left to say.
    - `SkReset peer chan` — the peer's error has already been reported to
                       the program once (citations v6.12).  Reads answer 0 from here on,
                       exactly as they do once `rx` is `NFin` — so this
                       constructor changes NO read behaviour.  It exists
                       because those two are DIFFERENT TCP STATES and
                       collapsing them would be a wrong answer for the
                       send side.  A consumed FIN leaves the socket in
                       CLOSE_WAIT, which is in `tcp_sendmsg_locked`'s
                       accepted mask `TCPF_ESTABLISHED | TCPF_CLOSE_WAIT`
                       and where a send SUCCEEDS; a consumed RST or
                       timeout ran net/ipv4/tcp.c `tcp_done`, leaving
                       TCP_CLOSE, where net/core/stream.c:
                       sk_stream_wait_connect answers -EPIPE.  Recording
                       the difference in the REPRESENTATION rather than
                       in a flag is the same move `NetStream`'s nullary
                       terminals make: the state that cannot send is a
                       different constructor, not a boolean somebody has
                       to remember to check.

    THE PER-CONNECTION STATE LIVES IN THE CONSTRUCTOR, not in fields
    beside it, so a listening socket cannot carry a byte stream and a
    fresh socket cannot carry a channel id: the states that have no
    stream have no place to put one.  And the socket state lives IN THE
    FD ENTRY rather than in a side table indexed by the entry, so
    `close` disposing of the fd disposes of the socket too — there is no
    table for a closed socket to leak into, and a reissued fd cannot
    inherit a dead peer's script. -/
inductive SockState where
  | SkFresh
  | SkBound
  | SkListening
  | SkConnected (peer : PeerAddr) (chan : word) (rx : NetStream)
  | SkReset (peer : PeerAddr) (chan : word)

/-- `PIPE_BUF` (include/uapi/linux/limits.h), which on riscv64 is also
    `PAGE_SIZE`: the size of the page a pipe buffers bytes in, and the
    largest transfer Linux writes atomically. -/
def PIPE_BUF : Int := 4096

/-- What the model records for one pipe: the bytes the queue currently
    holds, and how much of the PAGE those bytes live in has been written
    into — the merge high-water mark.

    Both are needed, and the second is the subtle one.  Everything this
    block asserts is fs/pipe.c at v6.18.46 (commit 1f99e9ab748f).  Linux
    buffers a pipe in whole pages held in a ring `alloc_pipe_info` sizes
    at `PIPE_DEF_BUFFERS` (:795, :824), whose value 16 is
    include/linux/pipe_fs_i.h, and counts fullness in
    SLOTS, not bytes (`pipe_full` against `pipe->max_usage`, :510).  A
    write tops up the last slot only when
    `buf->offset + buf->len + chars <= PAGE_SIZE` (`anon_pipe_write`'s
    merge test, :480-483), and a READ does not give that room back:
    `anon_pipe_read` advances `buf->offset` by exactly what it consumed
    and shortens `buf->len` (:350-351), leaving their SUM — the
    watermark — unchanged.  So the bytes a pipe can hold before it blocks
    is not 16 pages of data but a function of the write sizes: sixteen
    2049-byte writes fill it at 32784 bytes, and a pathological
    write/read alternation fills it at sixteen.  A byte-counted capacity
    would therefore admit full writes where Linux blocks.

    The model keeps the mark instead and stays inside ONE slot, which is
    the whole of what it has to prove: with `pipe_write_room` below, a
    modeled pipe's ring occupancy is never more than one, so `pipe_full`
    is never true and no modeled write can block.  A write that would
    need a second slot is declined rather than guessed at. -/
abbrev PipeBuf : Type := List byte × Int

/-- An open file descriptor, carrying its ACCESS MODE so the model can
    enforce -EBADF on wrong-direction I/O, as Linux does:

    - `FdChannel chan`: an external channel.  Channel fds only come from
      `init_model`, and their mode is determined by the channel id:
      stdin (0) is read-only, stdout (1) and stderr (2) are write-only.
      That is the direction PIPED STDIO has, and it is an ASSUMPTION
      about the environment rather than a fact about the fd number:
      Linux reads the direction off the description's `FMODE_*` bits,
      so a process handed a connected socket on fd 0 — every
      inetd-style server — may write it, and this model answers -EBADF.
    - `FdFile p off`: a file opened O_RDONLY (read-only); write is
      -EBADF.
    - `FdFileW p off`: a file opened O_WRONLY|O_CREAT|O_TRUNC
      (write-only); read is -EBADF.
    - `FdFileA p off`: a file opened O_WRONLY|O_CREAT|O_APPEND
      (write-only, APPEND MODE); read is -EBADF.  A SEPARATE
      CONSTRUCTOR RATHER THAN A FLAG ON `FdFileW`, and the reason is
      which arms have to notice.  The two kinds differ in where a write
      LANDS: `iocb_flags` (include/linux/fs.h) turns O_APPEND into
      IOCB_APPEND, and `generic_write_checks` (mm/filemap.c) then
      overwrites the iocb's position with `i_size_read(inode)`, so every
      write through this fd goes to the CURRENT end of the file whatever
      `off` says and whatever an `lseek` did to it (Linux v6.18.46).  A
      boolean field on `FdFileW` would leave every existing `FdFileW _ _`
      arm silently absorbing an append fd -- including
      `Fs.Fcntl.setfl_noop_on`, whose 0 for such an fd would be UNSOUND
      (see that definition).  A constructor makes each of those a compile
      error instead, which is the whole reason this type enumerates.

      `off` IS STILL CARRIED, and not because a write reads it: it is
      `f_pos`, which `lseek` still repositions and reports on an append
      fd, and which a write leaves at the new end of file.  Nothing
      derives a write POSITION from it.
    - `FdFileRW p off`: a file opened O_RDWR (READ-WRITE), possibly
      with O_CREAT, O_TRUNC or O_EXCL; see `Open.rdwr_open_word`.  It is
      the only file kind on which BOTH directions answer: a read is the
      `FdFile` arm and a write the `FdFileW` arm, at the one `f_pos`
      both of them advance.  That single shared position is the whole
      of what makes this a kind rather than a pair of fds: Linux keeps
      `f_pos` on the `struct file`, not on the access mode, so a read
      of n bytes moves the offset the next WRITE lands at, and a
      program that reads a header and then writes over the record after
      it depends on exactly that.

      A SEPARATE CONSTRUCTOR RATHER THAN A FLAG, for the reason the
      whole type enumerates: every existing `FdFile _ _` arm answers
      -EBADF to a write and every `FdFileW _ _` arm -EBADF to a read,
      and both of those are WRONG for this kind rather than
      conservative.  A flag would leave each of them absorbing an
      O_RDWR fd silently and reporting a -EBADF Linux never returns —
      a modeled wrong answer, not a gap.  A constructor makes each site
      a compile error.

      `off` IS AN ORDINARY `f_pos`, unlike `FdFileA`'s: reads and
      writes both start there and both advance it, and `lseek` moves
      it for either direction.
    - `FdDir`: a directory fd (from `openat` of "." or "..", the two
      paths that name a directory without a lookup; see
      `Open.path_is_dirref`).  It carries NO path, which is what makes
      those two answerable by one arm: nothing below can tell the
      working directory from its parent.  No I/O: read yields
      -EISDIR and write -EBADF, as Linux does on an O_RDONLY directory
      fd; directory enumeration (getdents64) answers only where nothing
      is listed — `filldir64`'s -EINVAL for a buffer too small for any
      entry — and the LISTING itself stays unmodeled and fail-closed,
      which is what keeps the missing path from mattering
      (`Readdir.getdents64_spec`).
    - `FdSocket sk`: an AF_INET/SOCK_STREAM socket, carrying its whole
      state (see `SockState`).  READABLE — a socket is never opened
      write-only, so the -EBADF gate must let it through and the read
      specs answer for it; a socket fd that failed that gate would
      report a FALSE -EBADF, which is a modeled wrong answer rather than
      a modeling gap.  WRITING one is unmodeled, permanently: on a reset
      connection write(2) returns -EPIPE *and raises SIGPIPE*, whose
      default action kills the thread group
      (net/core/stream.c `sk_stream_error`, kernel/signal.c `get_signal`),
      and a spec's outcomes are `Ok` and `Unmodeled` only — "the process
      died" has no encoding, and halting with 141 cannot be told apart
      from a voluntary exit(141).  The socket write path is
      sendto/sendmsg with MSG_NOSIGNAL, which is decidable from a
      syscall argument; it is not modeled here.
    - `FdPipe id writer`: ONE END of a pipe (from `pipe2`; see
      `Pipe.pipe2_spec`).  `id` names the pipe — BOTH ends carry the
      same one — and `writer` says which end this is: `false` is the
      read end (fd[0]; read-only, write is -EBADF) and `true` the write
      end (fd[1]; write-only, read is -EBADF).  That is fs/pipe.c's own
      split: `create_pipe_files` opens `res[0]` O_RDONLY and `res[1]`
      O_WRONLY, and `__do_pipe_flags` hands them back as `fd[0] = fdr`
      and `fd[1] = fdw`.  The buffered bytes live in the model's
      `m_pipes` side table, keyed by `id`, because they are shared
      BETWEEN the two ends: a byte written through the write end is read
      back through the read end, and neither fd owns it.  This is the
      first fd whose contents come from the program itself rather than
      from the environment or the file system.

      NOT EVERY SITE DISPATCHING ON FD KIND ANSWERS A PIPE END WITH
      MODELED BEHAVIOR.  Where this development has no derivation to
      offer — whether a pipe end is pollable, what `fstat` reports, what
      `clone` may do with one — the arm FAILS CLOSED and names what a
      real answer would have to be derived from, rather than guessing.
      An `FdEntry` match that a new constructor does not break is a
      match that would absorb it silently, so those sites enumerate.
    - `FdDevNull rd wr`: the character device /dev/null (major 1, minor
      3), opened by `Open.openat_spec`'s arm for exactly that pathname
      (`Uapi.devnull_path`).  It is the first descriptor whose object
      is a DEVICE rather than a file, a channel, a socket or a pipe,
      and the point of it is that it carries NOTHING: Linux's
      `null_fops` (drivers/char/mem.c, v6.18.46) reads 0 bytes
      (`read_null`), discards every write and reports the count
      (`write_null`), and pins `f_pos` at 0 on every `lseek`
      (`null_lseek`), so no modeled operation on the descriptor can
      observe a position, a buffer or a peer.  `rd` and `wr` are the
      access mode the open granted — `do_dentry_open` (fs/open.c) sets
      FMODE_READ and FMODE_WRITE from it — and they decide the one
      thing that IS observable: `vfs_read` and `vfs_write`
      (fs/read_write.c) answer -EBADF on a descriptor lacking the
      mode, ahead of the device.  `openat` mints `FdDevNull true false`
      for O_RDONLY, `false true` for O_WRONLY and `true true` for
      O_RDWR; `false false` is not constructible.

      THE ENVIRONMENT ASSUMPTION IT RESTS ON is stated at the openat
      arm and nowhere else: the environment's /dev/null is the null device.
      Every arm below that answers for this kind derives its answer
      from `null_fops` and the VFS path that reaches it, and every arm
      that cannot fails closed, so that a held-open /dev/null costs a
      run nothing and a program that does something with it the model
      has no derivation for is declined rather than guessed.
    - `FdUrandom`: the character device /dev/urandom (major 1, minor
      9), opened read-only by `Open.openat_spec`'s arm for exactly that
      pathname (`Uapi.urandom_path`); the write and read-write words
      are declined there, so the kind carries no access mode -- every
      descriptor of it has FMODE_READ and lacks FMODE_WRITE.  Its
      reads deliver the front of the run's DECLARED stream,
      `m_urandom` (seeded from `ProcInput`'s `in_urandom`), and advance
      it; the bytes are an input of the run, not a choice, and the
      same stream is read on both sides of an equivalence.  Linux's
      `urandom_fops` (drivers/char/random.c, v6.18.46) reads nothing
      off the `struct file` -- `urandom_read_iter` consults the
      generator and the iterator only, `noop_llseek` hands back an
      `f_pos` no modeled operation moves -- so nothing on the
      descriptor is observable beyond the bytes, and one stream serves
      every descriptor.  The arms that answer for it derive the answer
      from `urandom_fops` and the VFS path that reaches it; the rest
      fail closed.  THE ENVIRONMENT ASSUMPTION IT RESTS ON -- the
      environment's /dev/urandom is the random device -- is stated once, at
      the openat arm, and pointed to from everywhere else. -/
inductive FdEntry where
  | FdChannel (chan : word)
  | FdFile (p : Fs.path) (offset : word)
  | FdFileW (p : Fs.path) (offset : word)
  | FdFileA (p : Fs.path) (offset : word)
  | FdFileRW (p : Fs.path) (offset : word)
  | FdDir
  | FdSocket (sk : SockState)
  | FdPipe (id : word) (writer : Bool)
  | FdDevNull (rd wr : Bool)
  | FdUrandom

/-- Virtual-memory bookkeeping: a ledger of allocator decisions the model
    has already committed to (the flat byte-map memory can't encode
    "allocated but untouched").  Intervals are (base, size) pairs of
    words; all overlap/bound arithmetic on them happens in `Int` over
    `bv_unsigned` (see `iv_overlap`).  Seven purposes:
    (a) `vm_reserved` — the address space the kernel already used at
        `execve`: the page-rounded LOAD segments of the binary
        (`Run.segments_reserved`).  IMMUTABLE for the whole run, and held
        in a separate field on purpose: `munmap` removes `vm_maps`
        entries by base address, and a stray `munmap(seg_base, …)` must
        not be able to unreserve the binary image;
    (b) `vm_maps` — live anonymous mappings as `(lo, size)` intervals,
        including brk-grow grants — so allocator grants are handed out
        DISJOINT from each other and from the image (`region_free`
        against `vm_reserved ++ vm_maps`).  Read that as a PAGE-granular
        guarantee, which is what it is: no page-aligned address is ever
        owned by two entries, and every base a syscall can name is page
        aligned, so a base determines its entry.  Byte-level overlap IS
        reachable, because a brk grow within one page is checked by
        neither `region_free` nor Linux itself (see `live_bytes` below);
    (c) `vm_noaccess` — physical page ranges currently protected with
        PROT_NONE.  Ordinarily they are subranges of `vm_maps`.  A brk
        shrink within its final page is the deliberate exception: the
        byte-granular `vm_maps` tail is removed while Linux keeps the whole
        page mapped and protected, so `vm_noaccess` may transiently extend
        to `PAGE_ALIGN(vm_brk)`.  It still blocks placement through the
        containing brk page; mprotect also requires `vm_maps` containment,
        so the logical tail cannot be exposed until a same-page regrow owns
        it again.  Protected pages consume budget through their logical
        `vm_maps` ownership, and the machine overlay contains no bytes for
        them until a modeled mprotect makes them rw again;
    (d) `vm_start_brk` — Linux's `mm->start_brk`: the ASLR-placed base of
        the heap, set at `execve` (`Run.mi_init_brk`) and IMMUTABLE for
        the whole run.  It is the kernel's `min_brk`: a `brk` request
        below it is INVALID (returns the break unchanged), including
        requests in the ASLR gap between the image top and the base;
    (e) `vm_brk` — the CURRENT program break — to model `brk` (return the
        unchanged break, and anchor the zero-fill of a grow);
    (f) `vm_limit` — the BACKED-MEMORY BUDGET of this run, in bytes:
        no operation may push charged anonymous backing
        (`vm_backing_used`, including first-touched sparse pages) above it.
        Once the budget is spent, ordinary eager allocator operations admit
        only their failure resolutions; a MAP_NORESERVE grant may still
        reserve virtual space, but an access that would materialize another
        page takes the fault/error transition.  The
        out-of-memory point is forced, at a bound that is a function of
        the program's own grant/free history rather than of the
        quantified ASLR placements.  A parameter of the run
        (like the initial break), IMMUTABLE once seeded by
        `Run.mi_alloc_limit`; `Equivalence.strong_equiv` pins it to
        `source_alloc_limit`/`target_alloc_limit` per role, and a
        caller may seed smaller budgets to make
        exhaustion cheap to reach;
    (g) `vm_mmap_base` — Linux's `mm->mmap_base`: the top-down search
        bound of `get_unmapped_area`, set once at `execve`
        (`arch_pick_mmap_layout` via the generic mm/util.c layout — see
        `mmap_base_min`) and IMMUTABLE for the whole run.  Like the
        initial break it is a quantified parameter of the run
        (`Run.mi_mmap_base`, any `Run.valid_mmap_base` value,
        independent per binary).  NO SPEC ARM READS THIS FIELD'S VALUE.
        Preference-free placement says only
        that the address is page-aligned, inside the user address space
        and disjoint from every recorded mapping — a rule with no base
        in it (the argument is in `Mmap.mmap_spec`'s placement section).
        The field is NOT thereby inert and must not be removed as one:
        `Run.valid_mmap_base` is a conjunct of `Run.valid_entry`, which
        `Equivalence.strong_universal_T` quantifies its entries under,
        and discharging it is a required step of
        `Equivalence.image_brk_satisfiable_entry`, the tree's
        anti-vacuity lemma.  It is the PREDICATE that is load-bearing,
        not the value: no arm and no tier reads the value.
        A base of 0 is what `mkVmMaps` seeds and means only "no base
        recorded"; no state reachable from `State.init_model` under
        `Run.valid_mmap_base` carries it;
    (h) `vm_init_sp` — the stack pointer `execve` handed this run
        (`Run.mi_init_sp`, any `Run.valid_sp` value, quantified
        independently per binary), IMMUTABLE for the whole run.  The
        allocator reads it through `alloc_top` below: it is what keeps
        every grant off THIS run's stack.  The stack itself has no
        reservation entry — see `alloc_top` for why a bound does the
        job a reservation would. -/
structure VmMaps where
  mkVmMapsFull ::
  vm_reserved  : List (word × word)
  vm_maps      : List (word × word)
  vm_noaccess  : List (word × word)
  vm_start_brk : word
  vm_brk       : word
  vm_limit     : Int
  vm_mmap_base : word
  vm_init_sp   : word
  deriving DecidableEq, Repr

/-! ## The model subsystems -/

/-! `Model` IS A RECORD OF SUBSYSTEMS, not a flat list of fields, and the
    reason is the setters.  A flat record needs one setter per field and each
    one has to restate every field it does not change, so adding a field
    rewrites every setter -- and a change about clocks and a change about
    credentials collide over state neither one shares.  Nested, a new field
    inside a subsystem touches only that subsystem's record and its own
    setters.

    The accessors and `mkModel` below give a flat view, so nothing outside
    this file sees the nesting: `m_fds m` reads the fd table, and `mkModel`
    takes the seven components in order.

    ORDINARY PROJECTIONS, deliberately.  The example proofs reduce with
  explicit constant lists (``simp` [with_fds m_fds...]`), and `simp` with a
    list unfolds only what the list names -- which a PRIMITIVE projection
    cannot be.  Making these primitive would put the nesting beyond the reach
    of every such list.

  The fields carry NO default values: a default would turn the constructor into a
  function with extra implicit arguments and break positional construction
  (`mkModelOf …`, `mkModel …`). -/

/-- The open file descriptors, and the pipes some of them name.

    `fdst_pipes` is the PIPE BUFFERS, keyed by pipe id (see `pipe_lookup`).
    A side table rather than a payload on `FdEntry` because the queue is
    SHARED by two fds and outlives either of them (`close` of one end leaves
    the other end's view intact).  It sits in this subsystem because every
    reference to a pipe in this model is an fd in `fdst_table`, and the two
    are read together: which ends are still open is derived from the table
    (`pipe_end_live`) rather than counted.  Not observable: pipe bytes never
    reach the trace, so two runs that differ only in what a pipe holds are
    still equivalent — see `Pipe.pipe2_spec`.

  `fdst_table` holds `FdEntry`s, and `FdEntry` reaches `SockState` → `NetStream`,
  which the coinduction encoding makes a function (`Nat → NetStep`). Nothing needs
  it: `fd_lookup` compares KEYS with `bv_eqb`. -/
structure FdState where
  mkFdState ::
  fdst_table : List (word × FdEntry)
  fdst_pipes : List (word × PipeBuf)

/-- The virtual-memory subsystem.  `vmst_lazy` records page-aligned sparse
    anonymous reservations whose backing is charged on first data access;
    `vmst_materialized` is the deduplicated set of page bases already charged.
    These are process-accounting ledgers, not physical frames or page tables. -/
structure VmState where
  mkVmState ::
  vmst_maps : VmMaps
  vmst_lazy : List (word × word)
  vmst_materialized : List word
  deriving DecidableEq, Repr

/-- The channels.  Standard input carries the UNCONSUMED remainder of the
    run's input stream (see `InputStream`); the network carries the
    connections `accept` has not yet handed over, which is the same kind
    of thing for the same reason.

  `iost_stdin` and `iost_urandom` are
    `Nat → Option byte` and `iost_net` is a function too. -/
structure IoState where
  mkIoState ::
  /-- the UNCONSUMED remainder of the run's input stream -/
  iost_stdin : InputStream
  /-- the UNCONSUMED remainder of the random device's declared byte
      stream -- seeded from `in_urandom` and consumed by every read of
      an `FdUrandom` descriptor, exactly as `iost_stdin` is seeded from
      `in_stdin` and consumed by a read of channel 0.  One stream for
      the device rather than one per descriptor, because the
      declaration is about what the DEVICE hands out in order, and
      Linux's generator has no per-file state either
      (`urandom_read_iter`, drivers/char/random.c, v6.18.46, reads
      nothing off the `struct file`) -/
  iost_urandom : InputStream
  /-- the connections `accept` has NOT yet handed over — seeded from
      `in_net` and consumed one per successful accept, exactly as
      `iost_stdin` is seeded from `in_stdin` and consumed by read -/
  iost_net : NetQueue
  /-- how many connections `accept` HAS handed over.  Its only use is
      naming the trace channel of the next one: see
      `Net.Socket.conn_channel` -/
  iost_conn_ix : word

/-- The interpreted file system. -/
structure FsState where
  mkFsState ::
  fsst_image : Fs.Fs
  deriving DecidableEq, Repr

/-- The process's UNIX credentials.  Six ids, in the kernel's own
    grouping (include/linux/cred.h, `struct cred`): the REAL id, which
    says who owns the process; the EFFECTIVE id, which every permission
    check consults; and the SAVED set-id, which a process that has
    dropped its effective id may return to.  Each is a `word` holding a
    32-bit value, because every one of these syscalls declares its
    arguments `uid_t`/`gid_t` and the kernel truncates a 64-bit register
    to that width before it looks at the value (see `Syscall.uid32`).

    The kernel's `struct cred` carries fields this record does not, each
    because nothing the model can observe depends on it:

    - `fsuid`/`fsgid`, the ids filesystem permission checks use.  They
      follow `euid`/`egid` on every setter modeled here, and the model's
      file system (`Fs.Fs`) has no permission bits, so no modeled
      syscall can tell them apart from the effective ids.
    - the CAPABILITY sets.  See `creds_privileged` below for what the
      model puts in their place and what that assumes about the
      environment.

    The supplementary GROUP LIST *is* carried, as `cr_groups`, and the
    reason is `getgroups` (158): `Kernel.Groups.getgroups_spec` reports
    its LENGTH, so the list is observable.  The
    other two channels a real process could read it through stay shut —
    `Fs` has no group checks, and the model has no /proc, which is the
    least obvious of the three (fs/proc/array.c, `task_state`, the
    `Groups:` line).  Carrying the ELEMENTS as well as the length is
    deliberate: they are what `getgroups`'s array-writing form would
    copy out, and what `Kernel.Groups.setgroups_spec`'s successful half
    would write, so both of those declines are declines of the WRITE and
    not of the state.  A `Creds` that held only a count would have to
    change shape before either could be finished. -/
structure Creds where
  mkCreds ::
  /-- real user id -/
  cr_uid : word
  /-- effective user id -/
  cr_euid : word
  /-- saved set-user-id -/
  cr_suid : word
  /-- real group id -/
  cr_gid : word
  /-- effective group id -/
  cr_egid : word
  /-- saved set-group-id -/
  cr_sgid : word
  /-- the supplementary group list, in the order the kernel stores it:
      `struct group_info`'s `gid` array, whose `ngroups` is what
      `Sys.Kernel.Groups.getgroups_spec` reports.  Each element is a
      `gid_t`, which is `__kernel_gid32_t` and so 32 bits wide
      (include/uapi/asm-generic/posix_types.h), held in a `word` the
      same way the six ids above are. -/
  cr_groups : List word
  deriving DecidableEq, Repr

/-- The process itself: whether it has halted, its identity, who it runs
    as, and whether it has led a session. -/
structure ProcState where
  mkProcState ::
  /-- `some x` once the process is OVER.  Two
      ways to get there and the payload differs:
      after exit/exit_group it is the exit code
      (`Kernel.Exit.exit_spec`), and after a
      fatal signal it is the SIGNAL NUMBER
      (whichever of `Kernel.Signal.send_sigabrt`
      and `Kernel.Signal.sigmask_deliver_model`
      took it).
      `procst_killed` is what says which, and it
      is read by exactly two places --
      `Run.sstep_exit`, which declines a death by
      signal, and `Run.sstep_killed`, which
      takes it.  Every other rule reads only
      whether this field is `None`, which is the
      reason a kill writes it at all: a process
      that has been killed must stop executing
      instructions, and that is the premise those
      rules already carry -/
  procst_halted : Option word
  /-- the process identity, pinned by whichever
      of set_tid_address, getpid and a
      SUCCESSFUL setsid runs first; the kernel
      picks it at clone time, the model records
      it the first time it becomes observable,
      and every later query returns the same
      value.  That all three report the SAME
      value is not general: set_tid_address
      returns `task_pid_vnr(current)`, a tid,
      and setsid returns the group leader's
      vpid, a tgid.  They coincide because this
      model has one thread.  That rests on
      the clone FLAG WORD, not on the
      number: `clone` (220) and `clone3`
      (435) are modeled, but
      `Fork.clone_fork_flags_b` admits
      `SIGCHLD` alone and
      `Checks.ProcessCreation.clone_sharing_flags_unmodeled`
      (with
      `clone3_sharing_flags_unmodeled`
      the same for 435) forces
      `Unmodeled` on any bit of
      `clone_sharing_bits`, `CLONE_THREAD`
      among them.  Those two lemmas, and
      `clone_sharing_bits` itself, are the ones here
      in `Checks/ProcessCreation.v`, which **is not
      ported** (see the note above), so nothing
  here proves the force; what this tree has is
      `Fork.clone_fork_flags_b`'s closed word, read
      by inspection.  Widening that predicate
      would make this reading false rather than
      fail a proof -/
  procst_tid : Option word
  /-- the process's credentials: seeded from the
      run's `ProcInput` by `init_model` and
      mutated by the credential setters
      (`Kernel.Sys.setid_spec` and its
      siblings) -/
  procst_creds : Creds
  /-- whether a setsid has already succeeded,
      which is what makes every later one
      -EPERM.  Only a success is recorded: a
      failure can be followed by a success on a
      real kernel.  The asymmetry is
      `Kernel.Sys.setsid_spec`'s subject -/
  procst_setsid_succeeded : Bool
  /-- the signals the process has BLOCKED --
      Linux's `task_struct.blocked`, as the one
      64-bit word riscv64's `sigset_t` is
      (`Uapi.NSIG_BYTES` = 8, `_NSIG` = 64).
      Seeded from `ProcInput`'s `in_sigmask` by
      `init_model` and changed only by
      `Kernel.Signal.rt_sigprocmask_spec`.

      IT IS AN INPUT, NOT A CONSTANT, because
      execve does not reset the mask: `fs/exec.c`
      never names `blocked` and
      `begin_new_exec`'s `flush_signal_handlers`
      walks `sighand->action` only (Linux
      v6.18.46, commit 1f99e9ab748f).  So the
      mask a process starts with is entirely the
      launching environment's, exactly as
      `in_uid` and the ASLR'd stack pointer are.

      ONE WORD, NOT A BYTE LIST, the opposite of
      `limst_core`: that field is stored as bytes
      to avoid a round trip through a decoded
      pair, and this one is stored decoded
      because the three `how` arithmetics
      (`sigorsets`, `sigandnsets`, assignment --
      kernel/signal.c, `sigprocmask`) are
      bitwise operations on it.  The encoding
      happens once, where the mask is copied out
      to `oset` -/
  procst_sigmask : word
  /-- whether this process has acquired a child
      or a tracee.  `false` in `mkModel`;
      `Kernel.Fork.clone_resolve` sets it on its
      SUCCESS branch and nothing else does, so
      `Kernel.Exit.wait4_spec` stops answering
      -ECHILD for a process that now has
      something to reap.  See the launcher
      premise on `Kernel.Exit.wait4_spec`
      and `Checks.Examples.wait4_with_a_child_is_unmodeled`, which is the
      tripwire for it. -/
  procst_children : Bool
  /-- THE UTS NAME the process is told about, as the 390 bytes
      `uname` (160) copies out -- `struct new_utsname`, six 65-byte
      C-string fields (include/uapi/linux/utsname.h, Linux v6.18.46,
      commit 1f99e9ab748f) -- pinned the first time a `uname` READS
      it, exactly as `LimState.limst_core` pins RLIMIT_CORE and
      `procst_tid` pins the tid.  `None` means no `uname` has
      observed it yet.

      WHY IT IS PINNED RATHER THAN CHOSEN AFRESH.  Three of the six
      fields -- `nodename`, `release` and `version` -- are settled by
      the kernel BUILD and by the boot-time hostname, not by anything
      in kernel/sys.c, so the model cannot know them; but they do not
      change under a process either.  Nothing in
      `Specs.modeled_sysnos` writes one: `sethostname` (161) and
      `setdomainname` (162) have no dispatcher arm.  A `choose`
      resolved afresh at each call would therefore admit a trace in
      which two `uname` calls disagree about which kernel is running,
      which no Linux machine produces -- the same argument
      `Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec` makes for the
      CPU set it declines to answer for, and the note above `Record
      Model` is where the three mechanisms are compared.

      WHY IT IS PROCESS STATE.  Linux keeps it in the UTS NAMESPACE
      (`current->nsproxy->uts_ns->name`, include/linux/utsname.h's
      `utsname`), not in `task_struct`.  This model has exactly one
      process in exactly one namespace, so the distinction has nothing
      to bite on here; if a second namespace ever becomes reachable
      this field moves rather than gains a case.

      BYTES, NOT SIX DECODED STRINGS, for `limst_core`'s reason: the
      model only ever COPIES this field out, so storing it decoded
      would oblige the spec and the checker to agree on a round trip
      neither otherwise needs. -/
  procst_utsname : Option (List byte)
  /-- whether a `sigaltstack` has left
      `sas_ss_size` NON-ZERO -- an alternate
      stack is installed, not merely that the
      record has been assigned to.  `false` in
      `mkModel`: `execve` clears the stack
      (`begin_new_exec` sets
      `me->sas_ss_sp = me->sas_ss_size = 0`,
      fs/exec.c, Linux v6.18.46, commit
      1f99e9ab748f), so a starting process has
      none installed.

      ONE BIT, AND WHY ONE IS ALL THAT IS USABLE.
      `Kernel.Signal.sigaltstack_spec` answers
      only while the recorded SIZE is 0, because
      both of the record's readers take the USER
      STACK POINTER as an argument
      -- `on_sig_stack` and `sas_ss_flags`
      (include/linux/sched/signal.h) -- and
      `SyscallInput` carries a0..a5 and no sp.
      While `sas_ss_size` is 0 both answer the
      same thing for EVERY sp (not on the stack;
      SS_DISABLE); a size at or above
      `Uapi.MINSIGSTKSZ` ends that, and it is
      `do_sigaltstack`'s install branch alone
      that stores one.  So a stored
      `ss_sp`/`ss_size` would buy no answer this
      bit does not, and the spec declines once it
      is set.

      NOT EVERY SUCCESSFUL WRITE SETS IT.
      `do_sigaltstack` (kernel/signal.c) runs
      `ss_size = 0; ss_sp = NULL` before the
      store on its SS_DISABLE branch, so a
      disable assigns all three fields and still
      leaves the answerable (NULL, 0, ss_flags)
      shape.  The bit stays `false` there on
      purpose: setting it would decline calls
      the model can still answer.  What the
      invariant says is that while it is `false`
      the record is (NULL, 0, F) for some flags
      word F this model does not track, and
      every arm of the spec answers the same for
      every F. -/
  procst_sigaltstack_installed : Bool
  /-- whether the halt above is a DEATH BY SIGNAL
      rather than an exit.  The process was
      terminated by the signal `procst_halted`
      carries, with the default disposition,
      which a waiting parent reads as WIFSIGNALED
      and a shell renders as 128+that number.

      A FLAG BESIDE `procst_halted` RATHER THAN A
      SECOND `option word`, and the reason is the
      invariant it makes free: `m_killed` below
      reads this field THROUGH `procst_halted`,
      so "a killed process is over" holds by
      construction rather than by everybody
      remembering to write both -- see
      `m_killed_of_m_halted_none`, which is the
      fact every one-step inversion in
      `Common/` uses to rule the kill rule
      out of a configuration that is still
      running.  Two independent `option`s would
      make that a proof obligation on each
      writer, and a writer that forgot it would
      break no proof.

      ONLY `State.with_killed` sets it, its only
      callers are in
      `Sys.Kernel.Signal`, and SIGABRT is the only
      signal any of them sends --
      `Kernel.Signal.tkill_spec` is the one arm
      that can send a signal at all. -/
  procst_killed : Bool
  /-- SIGABRT has been sent to this process and
      is BLOCKED, so it sits in
      `task->pending.signal` waiting for the mask
      to let it through (kernel/signal.c,
      `send_signal_locked`; Linux v6.18.46,
      commit 1f99e9ab748f).

      A BOOL AND NOT A SIGSET, because at most
      one signal can ever be in it: the only arm
      that sends a signal is
      `Kernel.Signal.tkill_spec`, and the only
      signal it sends is SIGABRT.  A `sigset_t`
      here would be a field whose other 63 bits
      no reachable state can set, and the name
      would stop saying that.  The day a second
      signal becomes sendable this widens rather
      than gains a case.

      WHY THE STATE EXISTS AT ALL, given that the
      model delivers no signals from outside: it
      is where musl's `abort` leaves SIGABRT.
      `raise` blocks the application signals
      first, SIGABRT among them, so the `tkill`
      lands on a BLOCKED signal and the process
      does not die there; it dies on the return
      path from the `rt_sigprocmask` that
      restores the old mask.  Without this field
      the abort path could only be declined -/
  procst_sigabrt_pending : Bool
  /-- THE ONE FIELD OF THIS RECORD THAT IS NOT
      KERNEL STATE.  It is the task's
      declaration of whether the model covers the
      abort path at all, seeded by `init_model`
      from `ProcInput`'s `in_abort_terminal` and
      written by nothing.  `false` -- what
      `Run.valid_input` pins --
      makes `Kernel.Signal.tkill_spec` decline
      every call, as if 130 and 131 had no arm
      at all.

      WHY IT RIDES IN THE MODEL rather than
      beside `Run.SpuriousCfg`: that
      configuration FILTERS outcomes a spec
      already admits, so it can live outside the
      model and be applied at `Run.sstep_cfg`.
      This one decides what a spec admits, so it
      has to reach the spec, and the only channel
      a spec has to the run's parameters is the
      model.  `Run.valid_input` and
      `Run.valid_input_abort` are what put it in
      the STATEMENT, where a reader can see which
      stance a proof was made under; a statement
      that pins neither asserts both -/
  procst_abort_terminal : Bool
  /-- THE `struct stat` EACH STATTED FILE WAS FIRST SEEN WITH, keyed by
      path -- the 128 bytes `Fs.Stat.fstat_spec` delivered the first
      time that file was statted, kept so that a LATER stat of the same
      file cannot disagree with it about which file it is.  A path with
      no entry has not been statted yet.

      WHY A PIN AT ALL, and it is `procst_utsname`'s argument on a
      different value.  Of the twenty members of the delivered struct
      the model derives one, `st_size`, and knows four more to be zero
      padding; the rest -- the device, the inode, the mode, the link
      count, the owning ids, the block size, the block count and the
      three timestamps -- are the environment's, because `Fs.Fs` is a
      map from path to CONTENTS and carries none of them.  Chosen
      AFRESH at each call they would admit a trace in which two
      `fstat`s of one unchanged file report different inodes, which no
      Linux machine produces.  Chosen ONCE and recorded, they cannot.

      ONLY THE STABLE MEMBERS ARE HELD AGAINST A LATER CALL, and which
      those are is `Uapi.stat_stable_eqb`'s subject rather than this
      field's: the whole 128 bytes are stored, and the comparison
      ignores `st_size`, `st_blocks` and the timestamps, every one of
      which a write moves.  Storing the whole buffer and comparing part
      of it -- rather than storing a projection -- keeps the two halves
      of that decision in one place, next to the layout they are
      offsets into.

      NOT IN `Fs`, DELIBERATELY.  `Fs.Fs` is `ExitEv`'s payload and is
      compared with `=` (Fs.lean, CANONICAL FORM), so a nondeterministic
      value inside it would cost the examples statements they prove
      -- `Examples.cp_ns`'s `m_fs model = fs_set fs0v dstp
      (firstn k D)` is not provable if `fs_set` does not determine
      its result.  That is
      why the pin lives here: process state is observed by no
      event.

      KEYED BY PATH, WHICH IS THIS MODEL'S INODE.  Linux keys it by
      inode, and the difference shows only where two paths name one
      inode or one path names two -- neither of which `Fs`'s flat,
      link-free namespace can express (Fs.lean). -/
  procst_statpins : List (Fs.path × List byte)

/-- The resource limits the process has been observed to have. -/
structure LimState where
  mkLimState ::
  /-- RLIMIT_CORE as the 16 bytes of the `struct rlimit64` the kernel would
      copy out, pinned the first time a prlimit64 READS it, exactly as
      `procst_tid` pins the tid.  The limits a process starts with are
      inherited from its parent, so the model does not know them a priori:
      the environment chooses the pair (the kernel maintains soft <= hard)
      and the model records it, after which every later read returns it and
      a modeled set replaces it.  `None` means no prlimit64 has observed it
      yet.

      BYTES, NOT A DECODED PAIR, so the model only ever DECODES a limit and
      never re-encodes one; storing `(soft, hard)` would oblige the spec and
      the checker to agree on a round trip neither otherwise needs.

      `prlimit64` ANSWERS ONLY RLIMIT_CORE, and that is a separate matter
      from which limits this record carries: `limst_nofile` below is a
      limit the model KNOWS and `prlimit64` still declines. -/
  limst_core : Option (List byte)
  /-- RLIMIT_NOFILE's SOFT limit, `rlim_cur`, as an `unsigned long` -- the
      width `rlimit()` returns (include/linux/sched/signal.h,
      `task_rlimit`, Linux v6.18.46, commit 1f99e9ab748f).

      AN INPUT OF THE RUN, not an observation: unlike `limst_core`, which
      is pinned the first time a prlimit64 reads it, this one is seeded by
      `init_model` from `ProcInput`'s `in_nofile` and never changes.  It
      has to be an input for the same reason the launching uid is one --
      the limits a process starts with are its parent's, so the model does
      not know them and quantifies over them instead.  It never changes
      because no syscall in `Specs.modeled_sysnos` writes one: `setrlimit`
      (164) has no dispatcher arm, and `prlimit64` (261) has one but
      answers only RLIMIT_CORE.  An arm that answered a NOFILE set would
      have to make this field mutable, and `Sys.Fs.File.dup3_spec` is
      where the cost of that would land.

      ONLY THE SOFT LIMIT.  `rlim_max` is not carried because nothing
      reads it: `ksys_dup3` tests `rlimit(RLIMIT_NOFILE)`, which is
      `rlim_cur`, and the one syscall that would report the pair
      (`prlimit64`) declines this resource.  That decline is therefore
      load-bearing in both directions -- it is why the hard limit may be
      absent, and answering it would need the field. -/
  limst_nofile : word
  deriving DecidableEq, Repr

/-- The clocks the process can read. -/
structure TimeState where
  mkTimeState ::
  /-- CLOCK_MONOTONIC, in NANOSECONDS.  Held in state, rather than chosen
      afresh per call, because MONOTONICITY IS THE GUARANTEE: the field
      exists so that a later reading can be required not to precede an
      earlier one, which a per-call choice has nothing to compare against.
      It counts from an unspecified origin, so its absolute value means
      nothing and only differences do; the model starts it at 0, one of the
      origins Linux is free to pick.  See
      `Kernel.Time.PosixTimers.clock_gettime_spec`. -/
  timest_clock : word
  deriving DecidableEq, Repr

/-- THREE WAYS THIS MODEL CARRIES A FACT IT CANNOT KNOW A PRIORI, and
    nothing above says how to choose between them, which is what this
    note is for.  Each field below already argues its own case; what was
    missing is the comparison, and a new environment fact is the one
    place the wrong choice is cheap to make and expensive to find.

    - QUANTIFIED INPUT.  A `ProcInput` field, seeded by `init_model` —
      the record is the list, so none is written here.  The obligation
      quantifies over the input, so the theorem holds for every value
      the launching environment could have chosen that satisfies
      `Run.valid_input`; the bound is part of the claim and
      `limst_nofile`'s comment names its own.  Right when the LAUNCHING
      ENVIRONMENT settles the value, whether or not the program can
      later change it — several of these are mutable afterwards.
    - PINNED AT FIRST OBSERVATION.  `limst_core`, `procst_tid` and
      `procst_utsname`, each
      of which names its own trigger.  The environment chooses, the
      model records what it revealed, and every later query must answer
      the same.  Right when the value is NOT settled in the input —
      because nothing constructing a run would know to supply it — but
      must be self-consistent once seen.
    - CARRIED AND ADVANCED.  `timest_clock`, whose own comment gives the
      reason.  Right when the constraint is BETWEEN observations rather
      than on any one of them.

    The first two are already contrasted in place, most sharply by
    `limst_nofile`, which calls itself an input "unlike `limst_core`,
    which is pinned the first time a prlimit64 reads it" — two fields of
    ONE record taking opposite answers.  What no field can say, and the
    reason this note exists, is which answer a NEW one should take.

    THE PENDING CASE, named because it is what made this note worth
    writing: `Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec` declines
    for want of a CPU set, and wants the SECOND mechanism — its own
    spec argues why, and is not repeated here.  Naming that is not the
    same as building it, and it is not built. -/
structure Model where
  mkModelOf ::
  m_fd   : FdState
  m_vm   : VmState
  m_io   : IoState
  m_fsys : FsState
  m_proc : ProcState
  m_lim  : LimState
  m_time : TimeState

/- =========================================================================
   Observable trace events
   ========================================================================= -/

/-- The observables are BYTE-LEVEL channel I/O plus exit.  Bytes are
    `bv 8`; channel ids and the exit code are `word`. -/
inductive event where
  | ReadEv (ch : word) (b : byte)
  | WriteEv (ch : word) (b : byte)
  | ExitEv (code : word) (fs : Fs.Fs)
  | KillEv (sig : word) (fs : Fs.Fs)
  deriving DecidableEq, Repr

/- `KillEv` is the OTHER way a process ends: killed by `sig` with the
    default disposition, which is what a waiting parent reads as
    WIFSIGNALED and a shell renders as 128+`sig`.  It carries the final
    file system for `ExitEv`'s reason and it is a SEPARATE constructor for
    a reason of its own: `exit(134)` and a death by SIGABRT are different
    events to everything that observes this process, and folding the
    second into the first would make a model in which a program can fake
    its own abort.  The only rule that emits one is `Run.sstep_killed`,
    and the only signal that reaches it is SIGABRT -- see
    `procst_killed`. -/


/-! ## Numeric helpers (Linux riscv64 ABI conventions) -/

/-- 2^64, the width of `word`. -/
def two_pow_64 : Int := 2 ^ 64

def page_size : Int := 4096

/-- Page rounding, in `Int` over unsigned values (a length within a page
    of 2^64 would wrap under `BitVec` arithmetic; `Int` does not wrap, and
    the allocator bound checks below rely on that). -/
def page_round_up_Z (n : Int) : Int := ((n + page_size - 1) / page_size * page_size)

def page_round_down_Z (n : Int) : Int := (n / page_size * page_size)

/-- A nonzero length rounds up to at least one whole page. -/
theorem page_round_up_Z_pos (n : Int) (h : 0 < n) : page_size ≤ page_round_up_Z n := by
  unfold page_round_up_Z page_size
  have h1 : (4096 : Int) / 4096 ≤ (n + 4096 - 1) / 4096 :=
    Int.ediv_le_ediv (by omega) (by omega)
  have h1' : (1 : Int) ≤ (n + 4096 - 1) / 4096 := by simpa using h1
  have := Int.mul_le_mul_of_nonneg_right h1' (by omega : (0 : Int) ≤ 4096)
  simpa using this

/-- A page-aligned window swallows whole pages: if `x` lies in `[lo, hi)`
    and both ends are page aligned, so is the whole page `x` is on. -/
theorem page_round_down_Z_within (lo hi x : Int)
    (Hlo : lo % page_size = 0) (Hhi : hi % page_size = 0)
    (Hx : lo ≤ x ∧ x < hi) :
    lo ≤ page_round_down_Z x ∧ page_round_down_Z x + page_size ≤ hi := by
  unfold page_round_down_Z page_size at *
  have hlo := Int.mul_ediv_add_emod lo 4096
  have hhi := Int.mul_ediv_add_emod hi 4096
  have hx := Int.mul_ediv_add_emod x 4096
  have hmx0 := Int.emod_nonneg x (by omega : (4096 : Int) ≠ 0)
  have hmx1 := Int.emod_lt_of_pos x (by omega : (0 : Int) < 4096)
  constructor <;> omega

/-- Maximum dynamic stack size below the initial SP (Linux default
    `RLIMIT_STACK` = 8 MiB). -/
def stack_max_size : Int := 8 * 1024 * 1024

/-- The Sv48 initial-stack window.  `sp_window_hi` is `STACK_TOP =
    DEFAULT_MAP_WINDOW = 1 << (MMAP_VA_BITS - 1)` = 0x8000_0000_0000;
    `sp_window_lo` is 2 GiB below it, covering the 1 GiB of
    `randomize_stack_top` plus the largest admissible image.  An Sv39
    kernel puts STACK_TOP at 0x40_0000_0000 instead; the model is about
    the Sv48 configuration. -/
def sp_window_lo : Int := 0x7fff80000000
def sp_window_hi : Int := 0x800000000000

/-- Maximum ASLR displacement of the initial program break above the
    page-rounded image top: 1 GiB.  `load_elf_binary` moves the break one
    page up and `arch_randomize_brk`/`randomize_page(_, SZ_1G)` adds at
    most 1 GiB minus one page; the band's floor is the page-rounded image
    top itself (qemu-user's placement). -/
def brk_aslr_max : Int := 1 * 1024 * 1024 * 1024

/-- MMAP-BASE FLOOR: the smallest `mm->mmap_base` any covered kernel
    computes for a top-down layout = 0x154555557000.  Derived from
    `STACK_TOP - MAX_GAP - rnd` with `MIN_GAP = SZ_128M`,
    `MAX_GAP = STACK_TOP/6*5`, and `ARCH_MMAP_RND_BITS_MAX = 24`. -/
def mmap_base_min : Int := 0x154555557000

/-- MMAP-BASE CAP: the largest `mm->mmap_base` for a top-down layout =
    `STACK_TOP - MIN_GAP` = 0x7ffff8000000. -/
def mmap_base_max : Int := sp_window_hi - 128 * 1024 * 1024

/-- The top of the user address space, `TASK_SIZE` = 2^47, which riscv64
    `access_ok` compares a user range against and `munmap` refuses past.
    This is the Sv48 kernel's number; `__access_ok` is
    `size ≤ TASK_SIZE_MAX && addr ≤ TASK_SIZE_MAX - size`, and v6.18.46
    is outside the `TASK_SIZE_MAX = LONG_MAX` window. -/
def TASK_SIZE : Int := 0x800000000000

/-- `TASK_SIZE_64` per page-table depth.  `Sv48` is `TASK_SIZE` itself. -/
def va_task_size : VaSize → Int
  | .Sv39 => sv39_task_size
  | .Sv48 => TASK_SIZE
  | .Sv57 => sv57_task_size

/-- `STACK_TOP` per depth; Sv48 and Sv57 share it (`MMAP_VA_BITS` is
    capped at 48). -/
def va_stack_top : VaSize → Int
  | .Sv39 => sv39_task_size
  | .Sv48 => sp_window_hi
  | .Sv57 => sp_window_hi

def va_sp_window_hi (v : VaSize) : Int := va_stack_top v

def va_sp_window_lo (v : VaSize) : Int := va_stack_top v - 2 * 1024 * 1024 * 1024

def va_mmap_base_max (v : VaSize) : Int := va_stack_top v - 128 * 1024 * 1024

/-- Under Sv39 `mmap_base`'s own subtraction can wrap, so no positive
    floor holds of every draw; the Sv39 instance admits any page-aligned
    base up to the cap rather than a floor that would exclude a real one.
    (The floor is read by no arm.) -/
def va_mmap_base_min : VaSize → Int
  | .Sv39 => 0
  | .Sv48 => mmap_base_min
  | .Sv57 => mmap_base_min

/-- Anonymous backing budgets: 16 GiB for a source run, 512 GiB for a
    target (32x headroom).  Fixed constants, so the out-of-memory point
    of an unbounded allocator is forced. -/
def source_alloc_limit : Int := 0x400000000

def target_alloc_limit : Int := 0x8000000000

/-- a0 encodes a kernel error iff it is `-errno` for errno in [1,4095]
    (two's complement in 64 bits). -/
def addr_is_error_b (ret : word) : Bool :=
  two_pow_64 - 4096 < (ret.toNat : Int)

/-- `-e` as the 64-bit return register value. -/
def errno_ret (e : Int) : word := BitVec.ofInt 64 (-e)


end LinuxSem.LinuxProcessSem
