/-
  * LinuxProcessSem.Sys.Kernel.Groups — getgroups (158) and setgroups (159)


  This file answers to Linux [kernel/groups.c]: it holds what the
  kernel defines there, and nothing else.  Which file a spec belongs
  in is therefore not a judgement call — look up where the kernel
  defines the syscall.  [Specs.v] carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  [Specs.v] holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  What each dependency supplies:

      From LinuxSem.LinuxProcessSem Require Import BvBase Fs State Monad.
      From LinuxSem.LinuxProcessSem.Sys Require Export
        Syscall Uapi Uaccess.

  and opens the `sys`/`bv` scopes.  Here:

  - `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
    so a spec's type is `SysSpec SyscallEffect`, and `getModelSpec` is the
    monad's state accessor;
  - `Sys.Syscall` supplies `ret_only`, `err_ret` and `sint32`;
  - `Sys.Uapi` supplies `NGROUPS_MAX`;
  - `StateLedger` supplies `m_creds`, `creds_privileged`, `with_creds`
    and `mkModel` (chunk B5 of `State.v`).

  `Sys.Uaccess` is not imported: the only user buffer this file could
  name belongs to the DECLINED write arm, which no modeled path reads.
  Both `Sys.Uapi` and `Sys.Syscall` carry a local `abi_low32`/`fd32`
  (see their NOTEs); neither is used here.

  MONAD NOTATION.  `x <- c ;; k` has no Lean
  counterpart, so it is `bind c (fun x => k)` here.  `Z_to_bv 64 z` is
  `BitVec.ofInt 64 z`, `Z.of_nat n` is `(n : Int)`, and the `Z` tests
  `<?` / `=?` are the `Int` comparisons themselves (`if n < 0 then …`,
  `if n = 0 then …`): the same decision `decide (· < ·)` performs, with
  the `Bool` unboxed — the form the sanity checks below read.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Groups

/-! ## getgroups (158) -/

/-- [getgroups gidsetsize grouplist] (158): how many supplementary
    groups the process has, and — on a path this spec DECLINES — the
    groups themselves.

    THE WHOLE KERNEL FUNCTION, in its own order (Linux, kernel/groups.c,
    [SYSCALL_DEFINE2(getgroups)] and the one helper it calls,
    [groups_to_user]):

      if (gidsetsize < 0)            return -EINVAL;
      i = cred->group_info->ngroups;
      if (gidsetsize) {
        if (i > gidsetsize)          { i = -EINVAL; goto out; }
        if (groups_to_user(grouplist, cred->group_info))
                                     { i = -EFAULT; goto out; }
      }
      out: return i;

    Both functions are byte-identical from v4.9 through v6.18.
    [groups_to_user] last changed at commit 81243eacfa40 ("cred:
    simpler, 1D supplementary groups", first released in v4.9), a
    [GROUP_AT(group_info, i)] to [group_info->gid[i]] refactor with no
    behavioral change; the [getgroups] body has not changed since
    commit 30639b6af85a moved it into kernel/groups.c for v2.6.31.  The
    claim is over the WHOLE INTERVAL rather than its endpoints, which is
    the only form worth stating: the file's commit history since
    v2.6.31 contains no change to a line inside either function, and no
    stable branch backports one.  Tags read: v4.9, v5.4, v5.10, v5.15,
    v6.1, v6.6, v6.12, v6.16 and mainline master; stable branches read:
    linux-4.19.y, 5.4.y, 5.10.y, 5.15.y, 6.1.y, 6.6.y, 6.12.y.

    ORDER IS THE POINT HERE, three times over.

    - The NEGATIVE SIZE is refused before [current_cred()->group_info]
      is even read, so a negative [gidsetsize] with a garbage
      [grouplist] is -EINVAL and never -EFAULT.
    - A SIZE OF ZERO skips the whole [if (gidsetsize)] block, so the
      pointer is not touched at any width: [getgroups(0, <anything>)]
      answers the count.  That is the form musl's [getgroups] wrapper
      passes through unchanged (musl 1.2.5, src/unistd/getgroups.c) and
      the form dropbear's non-multiuser sanity check uses.
    - A SIZE TOO SMALL is -EINVAL BEFORE any store, so [getgroups(1,
      <garbage>)] on a process with five groups is -EINVAL rather than
      -EFAULT.

    [gidsetsize] is an [int], so only the low half of a0 reaches these
    comparisons and it is read as two's complement: a0 = 2^32 is
    [gidsetsize = 0], not a huge positive ([__SC_CAST] in
    include/linux/syscalls.h, applied by [__SYSCALL_DEFINEx] out of
    arch/riscv/include/asm/syscall_wrapper.h).  [Syscall.sint32] is that
    reading.  [grouplist] is a full 64-bit pointer and is NOT an
    argument of this spec at all, which is the sharpest way to state
    what the arms below share: no modeled path reads it.

    THERE IS NO UPPER BOUND ON [gidsetsize].  [setgroups] rejects a size
    above [Uapi.NGROUPS_MAX]; [getgroups] does not test it at all, so
    [getgroups(70000, buf)] is the count on a process whose list fits
    and would be the write on one whose list does not.  Nothing below
    compares [n] against [NGROUPS_MAX] for that reason — the guard
    further down is on the STORED LIST's length, not on the argument.

    THE ZERO-LENGTH LIST IS THE SUBTLE ARM.  With [gidsetsize > 0] and
    no supplementary groups, control does enter the block, but
    [groups_to_user]'s loop runs [ngroups] times — zero — and returns 0
    without a single [put_user].  There is no up-front [access_ok] over
    the array; validation is per element, inside the loop.  So
    [getgroups(64, <a garbage pointer>)] returns 0, not -EFAULT, for a
    process with no supplementary groups, and this spec says so.

    DECLINED: [gidsetsize >= ngroups > 0], the path that WRITES.  It
    stores [ngroups] 4-byte [gid_t]s ascending from [grouplist], each
    through its own [put_user], and a fault at element k leaves elements
    0..k-1 written — the kernel does not roll back.  Modeling that
    exactly means either proving the whole array writable or proving the
    FIRST element's range refused by [access_ok], the way
    [Net.Socket.socketpair_spec] reasons about its two stores; the band
    between those is [unmodeled] either way, and unlike socketpair the
    array's length is not fixed.  Cost of the decline, stated plainly: a
    program that reads its own group list — [initgroups], [id], anything
    that calls [getgroups(n, buf)] with [n] large enough — leaves the
    modeled surface on that call.  A program that only asks HOW MANY
    does not.

    NOT MODELED EITHER, and not the same kind of gap:
    [from_kgid_munged] answers an unmappable gid with [overflowgid]
    rather than an errno, so the ELEMENT VALUES this spec does not hand
    out would depend on the caller's user namespace.  The model already
    assumes the init namespace with an identity map (see
    [State.creds_privileged] for the standing assumptions), where the
    munge is the identity.

    THE [NGROUPS_MAX] GUARD is a fail-closed answer to a state Linux
    cannot build.  [Uapi.NGROUPS_MAX] bounds every [struct group_info]
    the kernel will allocate, so a longer [State.cr_groups] describes no
    process; the count such a state would report might not even fit the
    [int] this syscall returns.  Rather than answer for it, the spec
    declines — after the negative-size check, because that check comes
    first in the kernel and an impossible state must not reorder a
    behavior. -/
def getgroups_spec (gidsetsize : word) : SysSpec SyscallEffect :=
  let n := sint32 gidsetsize
  if n < 0 then err_ret EINVAL
  else
    bind getModelSpec (fun m =>
      let ng : Int := ((m_creds m).cr_groups.length : Int)
      if NGROUPS_MAX < ng then unmodeled
      else if n = 0 then ret_only (BitVec.ofInt 64 ng)
      else if n < ng then err_ret EINVAL
      else if ng = 0 then ret_only (BitVec.ofInt 64 0)
      else unmodeled)

/-! ## setgroups (159) -/

/-- [setgroups gidsetsize grouplist] (159): -EPERM for an unprivileged
    caller, and FAIL CLOSED for a privileged one.  (Linux v6.18.46,
    commit 1f99e9ab748f, kernel/groups.c, [SYSCALL_DEFINE2(setgroups)] /
    [may_setgroups] / [groups_from_user]; the whole file is
    byte-identical there and at every mainline release tag from v6.10
    through v6.18.)  [State.creds_privileged] carries the standing
    assumptions that let an effective uid answer the capability question
    [may_setgroups] really asks.

    The -EPERM half is exact, and it is exact for a reason worth naming:
    [may_setgroups()] is the FIRST thing the syscall does, before the
    [gidsetsize] bound and before the pointer is touched.  So an
    unprivileged caller gets -EPERM whatever it passes — a negative size,
    a size past NGROUPS_MAX, an unmapped list — and the spec needs
    neither argument.  A model that checked the arguments first would
    answer -EINVAL or -EFAULT where the kernel answers -EPERM.

    The successful half is DECLINED rather than faked.  It writes the
    supplementary group list — [State.cr_groups], the list [getgroups]
    (158) above reports the length of — so accepting the call while
    discarding what it wrote would make the next [getgroups] answer for
    a list nobody set.  The model carries the list;
    what is missing is a per-element import from user memory with the
    kernel's index-ordered -EFAULT-before-EINVAL precedence, and
    [groups_sort]'s ascending reorder, which is observable because
    [getgroups] hands back the STORED order and not the written one.

    Cost of the decline, stated plainly: a source binary that drops
    privilege the way dropbear does — [setgroups] via [initgroups],
    then [setgid], then [setuid] — leaves the modeled surface at the
    first of those three, so it cannot be certified.  The
    [rt_sigprocmask] (135) pair
    musl wraps around every credential syscall (musl 1.2.5,
    src/thread/synccall.c) is answered, so it does not leave earlier. -/
def setgroups_spec : SysSpec SyscallEffect :=
  bind getModelSpec (fun m =>
    if creds_privileged (m_creds m) then unmodeled else err_ret EPERM)

/-! ## Sanity checks on the computable parts

    There is no closed computation to re-use in this file.  These pin the arms
    its prose makes claims about, one per claim: `getgroups(0, ·)` answers
    the count; `a0 = 2^32` reads as `gidsetsize = 0`; a negative size
    answers `-EINVAL` before anything else is read; a size too small
    answers `-EINVAL` BEFORE any store; a zero-length list answers 0 even
    for a `gidsetsize > 0`; the writing arm is declined; `gidsetsize` has
    no upper bound; the `NGROUPS_MAX` guard is on the STORED LIST, is
    strict at the bound, and comes after the sign check; and `setgroups`
    separates its two halves on `creds_privileged`.  The last two pin the
    byte encoding a `gid_t` store would carry — the thing the declined arm
    does not do.

    They are port checks, not reused lemmas. -/

/-- A model whose process has the given supplementary group list, with
    `mkModel`'s default (unprivileged) credentials: every id is
    `overflow_id`, so `creds_privileged` is false. -/
private def check_model (gs : List word) : Model :=
  with_creds
    { cr_uid := overflow_id, cr_euid := overflow_id, cr_suid := overflow_id
      cr_gid := overflow_id, cr_egid := overflow_id, cr_sgid := overflow_id
      cr_groups := gs }
    (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [])

/-- The same model with `euid = 0`: the one id `creds_privileged` reads. -/
private def check_model_root (gs : List word) : Model :=
  with_creds
    { cr_uid := overflow_id, cr_euid := BitVec.ofInt 64 0
      cr_suid := overflow_id
      cr_gid := overflow_id, cr_egid := overflow_id, cr_sgid := overflow_id
      cr_groups := gs }
    (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [])

/-- The count `getgroups` reports: the length of the model's stored list,
    read back as the `int` the syscall returns. -/
private theorem ngroups_check (gs : List word) :
    ((m_creds (check_model gs)).cr_groups.length : Int) = (gs.length : Int) :=
  rfl

/-- A syscall input with no argument registers and no mapped memory —
    `getgroups` reads neither. -/
private def check_input : SyscallInput :=
  { in_sysno := 0, in_args := [], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- `getgroups(0, <anything>)` answers the count: 2 here.  `grouplist` is
    not an argument of the spec, so none is supplied. -/
example :
    getgroups_spec 0 check_input (check_model [4, 5])
      (.ok (mkEffect (BitVec.ofInt 64 2) [] []) (check_model [4, 5]) []) := by
  have hsz : sint32 (0 : word) = 0 := by decide
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (0 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, NGROUPS_MAX]
  rfl

/-- `a0 = 2^32` is `gidsetsize = 0`, not a huge positive — the low-half
    two's-complement reading `sint32` performs, so this reaches the count
    arm with the same answer as a literal 0. -/
example :
    getgroups_spec (BitVec.ofInt 64 4294967296) check_input (check_model [4, 5])
      (.ok (mkEffect (BitVec.ofInt 64 2) [] []) (check_model [4, 5]) []) := by
  have hsz : sint32 (BitVec.ofInt 64 4294967296) = 0 := by decide
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (0 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, NGROUPS_MAX]
  rfl

/-- A negative `gidsetsize` is `-EINVAL`, and it is refused FIRST: this
    model has 2 groups, and the sign check still wins. -/
example :
    getgroups_spec (BitVec.ofInt 64 (-1)) check_input (check_model [4, 5])
      (.ok (mkEffect (errno_ret EINVAL) [] []) (check_model [4, 5]) []) := by
  have hneg : sint32 (BitVec.ofInt 64 (-1)) < 0 := by decide
  simp only [getgroups_spec]
  rw [ite_eq_left hneg]
  rfl

/-- …and it wins over the `NGROUPS_MAX` guard too: a state with more
    groups than the kernel could ever build does not reorder the sign
    check. -/
example :
    getgroups_spec (BitVec.ofInt 64 (-1)) check_input
        (check_model (List.replicate 65537 0))
      (.ok (mkEffect (errno_ret EINVAL) [] [])
        (check_model (List.replicate 65537 0)) []) := by
  have hneg : sint32 (BitVec.ofInt 64 (-1)) < 0 := by decide
  simp only [getgroups_spec]
  rw [ite_eq_left hneg]
  rfl

/-- A size TOO SMALL is `-EINVAL` BEFORE any store: 1 slot, 5 groups. -/
example :
    getgroups_spec 1 check_input (check_model [1, 2, 3, 4, 5])
      (.ok (mkEffect (errno_ret EINVAL) [] [])
        (check_model [1, 2, 3, 4, 5]) []) := by
  have hsz : sint32 (1 : word) = 1 := by decide
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (1 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, NGROUPS_MAX,
    show ¬ (1 : Int) = 0 by omega]
  rfl

/-- The ZERO-LENGTH LIST with `gidsetsize > 0` answers 0 and never
    touches the (unmodeled, and here absent) pointer. -/
example :
    getgroups_spec 64 check_input (check_model [])
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) (check_model []) []) := by
  have hsz : sint32 (64 : word) = 64 := by decide
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (64 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, NGROUPS_MAX,
    show ¬ (64 : Int) = 0 by omega, show ¬ (64 : Int) < 0 by omega]
  rfl

/-- THERE IS NO UPPER BOUND ON `gidsetsize`: 70000 is still the count on a
    process with no groups, not -EINVAL. -/
example :
    getgroups_spec (BitVec.ofInt 64 70000) check_input (check_model [])
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) (check_model []) []) := by
  have hsz : sint32 (BitVec.ofInt 64 70000) = 70000 := by decide
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (70000 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, NGROUPS_MAX,
    show ¬ (70000 : Int) = 0 by omega, show ¬ (70000 : Int) < 0 by omega]
  rfl

/-- The WRITING arm — `gidsetsize >= ngroups > 0` — is DECLINED. -/
example :
    getgroups_spec 64 check_input (check_model [4, 5]) .unmodeled := by
  have hsz : sint32 (64 : word) = 64 := by decide
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (64 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, NGROUPS_MAX,
    show ¬ (64 : Int) = 0 by omega, show ¬ (64 : Int) < 2 by omega]
  rfl

/-- The `NGROUPS_MAX` guard is on the STORED LIST, not on the argument: a
    list longer than any `struct group_info` the kernel builds is
    declined rather than answered. -/
example :
    getgroups_spec 0 check_input (check_model (List.replicate 65537 0))
      .unmodeled := by
  have hsz : sint32 (0 : word) = 0 := by decide
  have hlen : (List.replicate 65537 (0 : word)).length = 65537 := by
    rw [List.length_replicate]
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (0 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  rw [ngroups_check, hlen]
  rw [ite_eq_left (show NGROUPS_MAX < ((65537 : Nat) : Int) by decide)]
  rfl

/-- …and the guard is STRICT: exactly `NGROUPS_MAX` groups is a process the
    kernel can build, so the count is answered rather than declined. -/
example :
    getgroups_spec 0 check_input (check_model (List.replicate 65536 0))
      (.ok (mkEffect (BitVec.ofInt 64 65536) [] [])
        (check_model (List.replicate 65536 0)) []) := by
  have hsz : sint32 (0 : word) = 0 := by decide
  have hlen : (List.replicate 65536 (0 : word)).length = 65536 := by
    rw [List.length_replicate]
  simp only [getgroups_spec, hsz]
  rw [ite_eq_right (show ¬ (0 : Int) < 0 by omega)]
  simp only [getModelSpec, bind_getModel]
  rw [ngroups_check, hlen]
  rw [ite_eq_right (show ¬ NGROUPS_MAX < ((65536 : Nat) : Int) by decide)]
  rw [ite_true]
  rfl

/-- `setgroups` for an UNPRIVILEGED caller is -EPERM, and the spec reads
    neither argument to say so. -/
example :
    setgroups_spec check_input (check_model [4, 5])
      (.ok (mkEffect (errno_ret EPERM) [] []) (check_model [4, 5]) []) := by
  simp only [setgroups_spec, getModelSpec, bind_getModel]
  simp [check_model, with_creds, m_creds, creds_privileged, overflow_id]
  rfl

/-- …and the PRIVILEGED half is declined, not faked. -/
example : setgroups_spec check_input (check_model_root [4, 5]) .unmodeled := by
  simp only [setgroups_spec, getModelSpec, bind_getModel]
  simp [check_model_root, with_creds, m_creds, creds_privileged, overflow_id]
  rfl

/-- The byte encoding a `gid_t` store would carry, which the declined arm
    above does not perform: gid 1000 is four little-endian bytes. -/
example : Z_to_le_bytes 4 1000 = [(0xe8 : byte), (0x03 : byte), 0, 0] := by
  decide

/-- …as a write effect's payload would carry it (a `gid_t` is 4 bytes —
    include/uapi/asm-generic/posix_types.h, `__kernel_gid32_t`). -/
example :
    (mkEffect (BitVec.ofInt 64 2)
        [((4096 : word), Z_to_le_bytes 4 1000)] []).eff_writes
      = [((4096 : word), [(0xe8 : byte), (0x03 : byte), 0, 0])] := by
  decide

end LinuxSem.LinuxProcessSem.Sys.Kernel.Groups
