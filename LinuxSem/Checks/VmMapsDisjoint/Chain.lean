/-
  * LinuxSem.Checks.VmMapsDisjoint.Chain — THE DISPATCHER
    CHAIN: one invariant theorem for the whole syscall surface.

  WHAT THIS MODULE IS.  PART 3 proves the frame lemmas for the 90 arms of
  `checked_table`, and this module turns them into one statement about the
  dispatcher:

      `arm_preserves_vm`, one proposition per `CheckedArm`;
      `checked_table_preserves_vm`, the table statement;
      and the corollaries `check_syscall_preserves_vm_wf`,
      `syscall_spec_preserves_vm_wf`, `base_unique_after_syscall`.

  Everything below is that block.  It is the piece `LinuxProcessSem/
  StateLedger.lean` names by hand — it cites
  `Checks/VmMapsDisjoint.check_syscall_preserves_vm_wf` as the theorem that
  would discharge page-granularity disjointness for the syscall surface.
  That theorem is here, and it is proved from the arm lemmas, not assumed.

  HOW THE TABLE IS DISCHARGED.  `Chain/Arms.lean` carries one
  `arm_<name>_preserves_vm` per FRAME arm (86 of the 90, `brk` included),
  each the three lines `simp only [arm_X] at H` + the arm's frame lemma +
  `exact Hwf`; `Chain/Writers.lean` carries the four ledger-REBUILDING
  writers (`munmap`, `mremap`, `mmap`, `mprotect`) as
  `check_*_preserves`; this module lifts those four to `arm_*` form and
  assembles the 90-entry table.  Nothing here re-proves an arm.

  SPELLING, stated where it happens: Lean's core has NO
  `List.Forall` (see `Checks/Cases/Net/Socket.lean`, which declares the
  same two-constructor predicate for the same reason), so the table
  statement `Forall arm_preserves_vm checked_table` uses the `Forall`
  inductive declared below.  The `∀ c ∈ checked_table, …` form the
  dispatcher then consumes is derived from it once
  (`forall_mem_of_forall`), so both shapes are available and neither is
  stronger than the other.

  THE PAYOFF, in the order `StateLedger.lean` reads it:
  `check_syscall_preserves_vm_wf` is the checker-side result — an
  ACCEPTED syscall preserves `vm_wf`; `syscall_spec_preserves_vm_wf` is
  the same for the relational spec (through the completeness
  direction); and
  `base_unique_after_syscall` is what the invariant BUYS: after any
  syscall, a `map_has` hit at a page-aligned base names exactly one
  ledger entry (`base_entry_unique`, PART 2), which is the fact a
  downstream `munmap`/`mremap` argument reads.

  NO proof hole, no `decide` on the invariant (it is not a decidable
  proposition: it quantifies over the checker field).
-/

import LinuxSem.Checks.VmMapsDisjoint.Chain.Arms
import LinuxSem.Checks.VmMapsDisjoint.Chain.Writers

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.VmMapsDisjoint

namespace LinuxSem.Checks.VmMapsDisjoint

open LinuxSem.Common.RocqSpelling

/-- `List.Forall`, at the two constructors the table statement
    uses (`nil`, `cons`).  Lean's core list library has no such predicate,
    so it is declared here rather than restating the table statement —
    `Checks/Cases/Net/Socket.lean` records the same choice for the same
    reason. -/
inductive Forall {α : Type} (p : α → Prop) : List α → Prop where
  | nil : Forall p []
  | cons {a : α} {l : List α} (h : p a) (t : Forall p l) : Forall p (a :: l)

/-- The membership form the dispatcher reads, derived from the `Forall`
    once so that the table proof does not have to produce it as well. -/
theorem forall_mem_of_forall {α : Type} {l : List α} {p : α → Prop}
    (H : Forall p l) : ∀ a ∈ l, p a := by
  induction H with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons hx _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx
    · exact ih a ha

/-! ## The four writers, as `CheckedArm`s

    `Chain/Writers.lean` states their preservation over the CHECKERS
    (`check_munmap_preserves` …), which is where the ledger algebra lives;
    these four lines are the same `simp only [arm_X] at H` bridge the frame
    arms use. -/

theorem arm_munmap_preserves_vm : arm_preserves_vm arm_munmap := by
  intro i eff m m' evs H Hwf
  simp only [arm_munmap] at H
  exact check_munmap_preserves (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
    (Hwf := Hwf)

theorem arm_mremap_preserves_vm : arm_preserves_vm arm_mremap := by
  intro i eff m m' evs H Hwf
  simp only [arm_mremap] at H
  exact check_mremap_preserves (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
    (Hwf := Hwf)

theorem arm_mmap_preserves_vm : arm_preserves_vm arm_mmap := by
  intro i eff m m' evs H Hwf
  simp only [arm_mmap] at H
  exact check_mmap_preserves (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
    (Hwf := Hwf)

theorem arm_mprotect_preserves_vm : arm_preserves_vm arm_mprotect := by
  intro i eff m m' evs H Hwf
  simp only [arm_mprotect] at H
  exact check_mprotect_preserves (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
    (Hwf := Hwf)

/-! ## THE TABLE: all 90 arms, in `checked_table`'s own order

    `repeat' constructor` peels the `Forall` and leaves the 90 arm goals in
    table order, so each line below names exactly one arm's lemma — no arm
    can be silently dropped, because the count has to close. -/

theorem checked_table_preserves_vm : Forall arm_preserves_vm checked_table := by
  simp only [checked_table]
  repeat' constructor
  · exact arm_getcwd_preserves_vm
  · exact arm_eventfd2_preserves_vm
  · exact arm_epoll_create1_preserves_vm
  · exact arm_epoll_ctl_preserves_vm
  · exact arm_epoll_pwait_preserves_vm
  · exact arm_dup_preserves_vm
  · exact arm_dup3_preserves_vm
  · exact arm_fcntl_preserves_vm
  · exact arm_ioctl_preserves_vm
  · exact arm_flock_preserves_vm
  · exact arm_unlinkat_preserves_vm
  · exact arm_ftruncate_preserves_vm
  · exact arm_faccessat_preserves_vm
  · exact arm_openat_preserves_vm
  · exact arm_close_preserves_vm
  · exact arm_pipe2_preserves_vm
  · exact arm_getdents64_preserves_vm
  · exact arm_lseek_preserves_vm
  · exact arm_read_preserves_vm
  · exact arm_write_preserves_vm
  · exact arm_readv_preserves_vm
  · exact arm_writev_preserves_vm
  · exact arm_pread64_preserves_vm
  · exact arm_pwrite64_preserves_vm
  · exact arm_pselect6_preserves_vm
  · exact arm_ppoll_preserves_vm
  · exact arm_readlinkat_preserves_vm
  · exact arm_newfstatat_preserves_vm
  · exact arm_fstat_preserves_vm
  · exact arm_fsync_preserves_vm
  · exact arm_fdatasync_preserves_vm
  · exact arm_timerfd_create_preserves_vm
  · exact arm_exit_preserves_vm
  · exact arm_exit_group_preserves_vm
  · exact arm_set_tid_address_preserves_vm
  · exact arm_futex_preserves_vm
  · exact arm_nanosleep_preserves_vm
  · exact arm_clock_gettime_preserves_vm
  · exact arm_sched_setscheduler_preserves_vm
  · exact arm_sched_getaffinity_preserves_vm
  · exact arm_sched_yield_preserves_vm
  · exact arm_tkill_preserves_vm
  · exact arm_tgkill_preserves_vm
  · exact arm_sigaltstack_preserves_vm
  · exact arm_rt_sigaction_preserves_vm
  · exact arm_rt_sigprocmask_preserves_vm
  · exact arm_setgid_preserves_vm
  · exact arm_setuid_preserves_vm
  · exact arm_setresuid_preserves_vm
  · exact arm_setresgid_preserves_vm
  · exact arm_setsid_preserves_vm
  · exact arm_getgroups_preserves_vm
  · exact arm_setgroups_preserves_vm
  · exact arm_uname_preserves_vm
  · exact arm_prctl_preserves_vm
  · exact arm_gettimeofday_preserves_vm
  · exact arm_getpid_preserves_vm
  · exact arm_getuid_preserves_vm
  · exact arm_geteuid_preserves_vm
  · exact arm_getgid_preserves_vm
  · exact arm_getegid_preserves_vm
  · exact arm_gettid_preserves_vm
  · exact arm_socket_preserves_vm
  · exact arm_socketpair_preserves_vm
  · exact arm_bind_preserves_vm
  · exact arm_listen_preserves_vm
  · exact arm_accept_preserves_vm
  · exact arm_connect_preserves_vm
  · exact arm_getsockname_preserves_vm
  · exact arm_getpeername_preserves_vm
  · exact arm_sendto_preserves_vm
  · exact arm_recvfrom_preserves_vm
  · exact arm_setsockopt_preserves_vm
  · exact arm_getsockopt_preserves_vm
  · exact arm_shutdown_preserves_vm
  · exact arm_sendmsg_preserves_vm
  · exact arm_recvmsg_preserves_vm
  · exact arm_brk_preserves_vm
  · exact arm_munmap_preserves_vm
  · exact arm_mremap_preserves_vm
  · exact arm_clone_preserves_vm
  · exact arm_mmap_preserves_vm
  · exact arm_mprotect_preserves_vm
  · exact arm_madvise_preserves_vm
  · exact arm_accept4_preserves_vm
  · exact arm_wait4_preserves_vm
  · exact arm_prlimit64_preserves_vm
  · exact arm_getrandom_preserves_vm
  · exact arm_clone3_preserves_vm
  · exact arm_faccessat2_preserves_vm

/-- `checked_table_preserves_vm` in the membership form, which is what a
    lookup produces (`lookup_ca_In`). -/
theorem checked_table_preserves_vm_mem : ∀ c ∈ checked_table, arm_preserves_vm c :=
  forall_mem_of_forall checked_table_preserves_vm

/-! ## THE DISPATCHER COROLLARIES -/

/-- THE CHECKER-SIDE THEOREM.  Whatever arm `checked_table` answers for this
    syscall number, if it ACCEPTS then the invariant holds on the
    post-state.  This is the theorem `LinuxProcessSem/StateLedger.lean`
    cites as the one that discharges page-granularity disjointness for the
    modelled syscall surface: it is one application of the answered arm's
    `arm_preserves_vm`, which is one application of that arm's frame (or,
    for the five writers, of the ledger algebra).

    Note the shape: an UNMODELLED number makes the hypothesis impossible
    (`CheckUnmodeled ≠ CheckOk`), so no coverage premise is needed — the
    theorem is unconditional. -/
theorem check_syscall_preserves_vm_wf (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : CheckedTable.check_syscall i eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold CheckedTable.check_syscall at H
  unfold LinuxSem.Checks.Sys.Dispatch.check_syscall at H
  cases hlook : lookup_ca checked_table (i.in_sysno.toNat : Int) with
  | none =>
    rw [hlook] at H
    exact absurd H (by simp)
  | some c =>
    rw [hlook] at H
    exact checked_table_preserves_vm_mem c (lookup_ca_In checked_table _ c hlook)
      i eff m m' evs H Hwf

/-- THE SPEC-SIDE RESULT: the same statement for the relational spec,
    through the completeness direction
    (`CheckedTable.check_syscall_complete_ok`).  So the invariant is a
    property of ADMITTED
    syscalls, not only of the checker's answers. -/
theorem syscall_spec_preserves_vm_wf (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (H : Specs.syscall_spec i m (.ok eff m' evs))
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') :=
  check_syscall_preserves_vm_wf i eff m m' evs
    (CheckedTable.check_syscall_complete_ok i eff m m' evs H) Hwf

/-- WHAT THE INVARIANT BUYS, after ANY syscall: a `map_has` hit at a
    page-aligned base names exactly ONE ledger entry, and it is the one
    `map_has` matched.  This is `base_entry_unique` (PART 2) applied at the
    post-state, and it is the fact a downstream `munmap` / `mremap`
    argument reads — `map_remove`'s base-only removal and `map_has`'s
    `(base, size)` test name the same mapping. -/
theorem base_unique_after_syscall (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : CheckedTable.check_syscall i eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) (a n : word)
    (Ha : bv_unsigned a % page_size = 0)
    (Hhas : map_has (vm_maps (m_vmmaps m')) a n = true) :
    List.filter (fun q => bv_eqb q.1 a) (vm_maps (m_vmmaps m')) = [(a, n)] :=
  base_entry_unique _ a n (check_syscall_preserves_vm_wf i eff m m' evs H Hwf) Ha Hhas

/-- …and hence the SIZE in a `map_has` hit is unique after any syscall, the
    form the `munmap` frame argument uses. -/
theorem base_size_unique_after_syscall (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : CheckedTable.check_syscall i eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) (a n1 n2 : word)
    (Ha : bv_unsigned a % page_size = 0)
    (H1 : map_has (vm_maps (m_vmmaps m')) a n1 = true)
    (H2 : map_has (vm_maps (m_vmmaps m')) a n2 = true) : n1 = n2 :=
  map_has_pins_size _ a n1 n2
    (check_syscall_preserves_vm_wf i eff m m' evs H Hwf) Ha H1 H2

end LinuxSem.Checks.VmMapsDisjoint
