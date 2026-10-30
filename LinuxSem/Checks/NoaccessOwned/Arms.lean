/-
  * LinuxSem.Checks.NoaccessOwned.Arms — the base case and the whole
    dispatcher: `sys_inv` at `execve`, and one `Forall` over every arm of
    `checked_table`.

    `sys_inv h` is the three ledger invariants together — page-granular
    disjointness (`VmMapsDisjoint.vm_wf`), the end-inside-the-space bound
    (`MapsFit.vm_fit`) and the protected-byte cover (`na_inv`) — so the
    step is three walks over the same table.  Two of them already exist
    (`Chain/Arms.lean` + `Chain.lean` for `vm_wf`, `MapsFit.lean` for
    `vm_fit`); this module adds the third and puts them together.

    THE SHAPE.  An arm's `ca_check` field is a lambda around its checker, so
    `arm_preserves_na arm_X` is `simp only [arm_X] at H` — the arm record's
    TERM-level equation — followed by the arm's own lemma: for the 85 frame
    arms a `*_frame` (`m_vmmaps m' = m_vmmaps m`) and `na_inv_of_m_vmmaps`;
    for the five writers that rebuild the ledger, `check_*_preserves_na`.
    Nothing is re-proved per arm.
-/

import LinuxSem.Checks.NoaccessOwned.Writers

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.Sys.Kernel.Signal
open LinuxSem.Checks.VmMapsDisjoint
open LinuxSem.Checks.MapsFit
open LinuxSem.Checks.NoaccessOwned

namespace LinuxSem.Checks.NoaccessOwned

open LinuxSem.Common.RocqSpelling

/-! ## The base case: `execve`'s ledgers start empty -/

/-- The protected ledger starts empty, so `na_shape` is vacuous and so is
    `na_cover`. -/
theorem init_model_na_inv (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    na_inv (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) := by
  have hv : vm_noaccess (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = [] := rfl
  unfold na_inv na_inv'
  rw [hv]
  refine ⟨?_, ?_⟩
  · intro a n h
    exact absurd h (by simp)
  · intro a n x h
    exact absurd h (by simp)

/-- `sys_inv` at `execve`: the three invariants at the initial state. -/
theorem init_model_sys_inv (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    sys_inv (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) :=
  ⟨init_model_vm_wf reserved brk0 mbase sp lim inp,
   init_model_vm_fit reserved brk0 mbase sp lim inp,
   init_model_na_inv reserved brk0 mbase sp lim inp⟩


/-! ## The third walk: every arm of the table keeps `na_inv` -/

/-- A step that leaves the whole `VmMaps` record alone — the FRAME shape —
    preserves the cover, which reads `vm_maps` and `vm_noaccess` only. -/
theorem na_inv_of_m_vmmaps {m m' : Model} (h : m_vmmaps m' = m_vmmaps m)
    (H : na_inv (m_vmmaps m)) : na_inv (m_vmmaps m') := by
  rw [h]
  exact H

/-- THE ARM INVARIANT: the arm's checker keeps `na_inv`.  Stated over the
    `ca_check` FIELD, as `arm_preserves_vm` and `arm_preserves_fit` are, so
    the table statement can be a `Forall` over `checked_table`.  The three
    hypotheses are the arm's whole input invariant: the cover alone is not
    enough for the writers that remove an entry (`na_inv_munmap` needs
    `vm_wf`'s `map_has_unique`, and the cut leaves need `vm_fit`). -/
def arm_preserves_na (c : CheckedArm) : Prop :=
  ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event),
    c.ca_check i eff m = .CheckOk m' evs →
    vm_wf (m_vmmaps m) → vm_fit (m_vmmaps m) → na_inv (m_vmmaps m) →
    na_inv (m_vmmaps m')

/-- THE TABLE, all 90 arms in `checked_table`'s own order.  `repeat'
    constructor` peels the `Forall` and leaves one goal per arm in table
    order, so the count has to close: an arm cannot be silently dropped.

    Each arm is `Chain/Arms.lean`'s three steps — `simp only [arm_X] at H`
    (the arm record's TERM-level equation), then the arm's own lemma — with
    `na_inv` in place of `vm_wf`.  The `simp only` must be `simp only`: a
    bare `unfold arm_X at H` leaves the `ca_check` projection of the record
    literal unreduced, and the frame's word arguments (which occur only in
    `H`) then cannot be inferred — measured on `arm_listen` while porting
    `MapsFit`. -/
theorem checked_table_preserves_na : Forall arm_preserves_na checked_table := by
  simp only [checked_table]
  repeat' constructor
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getcwd] at H
    exact check_getcwd_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_eventfd2] at H
    exact check_eventfd2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_epoll_create1] at H
    exact check_epoll_create1_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_epoll_ctl] at H
    exact check_epoll_ctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_epoll_pwait] at H
    exact check_epoll_pwait_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_dup] at H
    exact check_dup_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_dup3] at H
    exact check_dup3_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_fcntl] at H
    exact check_fcntl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_ioctl] at H
    exact check_ioctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_flock] at H
    exact check_flock_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_unlinkat] at H
    exact check_unlinkat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_ftruncate] at H
    exact check_ftruncate_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_faccessat] at H
    exact check_faccessat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_openat] at H
    exact check_openat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_close] at H
    exact check_close_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_pipe2] at H
    exact check_pipe2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getdents64] at H
    exact check_getdents64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_lseek] at H
    exact check_lseek_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_read] at H
    exact check_read_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_write] at H
    exact check_write_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_readv] at H
    exact check_readv_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_writev] at H
    exact check_writev_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_pread64] at H
    exact check_pread64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_pwrite64] at H
    exact check_pwrite64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_pselect6] at H
    exact check_pselect6_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_ppoll] at H
    exact check_ppoll_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_readlinkat] at H
    exact check_readlinkat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_newfstatat] at H
    exact check_newfstatat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_fstat] at H
    exact check_fstat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_fsync] at H
    exact check_fsync_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_fdatasync] at H
    exact check_fsync_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_timerfd_create] at H
    exact check_timerfd_create_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_exit] at H
    exact check_exit_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_exit_group] at H
    exact check_exit_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_set_tid_address] at H
    exact check_set_tid_address_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_futex] at H
    exact check_futex_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_nanosleep] at H
    exact check_nanosleep_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_clock_gettime] at H
    exact check_clock_gettime_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_sched_setscheduler] at H
    exact check_sched_setscheduler_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_sched_getaffinity] at H
    exact check_sched_getaffinity_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_sched_yield] at H
    exact check_sched_yield_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_tkill] at H
    exact check_tkill_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_tgkill] at H
    exact check_tgkill_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_sigaltstack] at H
    exact check_sigaltstack_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_rt_sigaction] at H
    exact check_rt_sigaction_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_rt_sigprocmask] at H
    exact LinuxSem.Checks.VmMapsDisjoint.check_rt_sigprocmask_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setgid] at H
    exact check_setid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setuid] at H
    exact check_setid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setresuid] at H
    exact check_setresid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setresgid] at H
    exact check_setresid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setsid] at H
    exact check_setsid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getgroups] at H
    exact check_getgroups_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setgroups] at H
    exact check_setgroups_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_uname] at H
    exact check_uname_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_prctl] at H
    exact check_prctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_gettimeofday] at H
    exact check_gettimeofday_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getpid] at H
    exact check_getpid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getuid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_geteuid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getgid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getegid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_gettid] at H
    exact check_gettid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_socket] at H
    exact check_socket_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_socketpair] at H
    exact check_socketpair_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_bind] at H
    exact check_bind_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_listen] at H
    exact check_listen_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_accept] at H
    exact check_accept4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_connect] at H
    exact check_connect_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getsockname] at H
    exact check_getsockname_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getpeername] at H
    exact check_getpeername_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_sendto] at H
    exact check_sendto_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_recvfrom] at H
    exact check_recvfrom_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_setsockopt] at H
    exact check_setsockopt_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getsockopt] at H
    exact check_getsockopt_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_shutdown] at H
    exact check_shutdown_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_sendmsg] at H
    exact check_sendmsg_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_recvmsg] at H
    exact check_recvmsg_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    simp only [arm_brk] at H
    exact check_brk_preserves_na (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (_Hwf := Hwf) (Hfit := Hfit) (Hna := Hna)
  · intro i eff m m' evs H Hwf Hfit Hna
    simp only [arm_munmap] at H
    exact check_munmap_preserves_na (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hwf := Hwf) (Hfit := Hfit) (Hna := Hna)
  · intro i eff m m' evs H Hwf Hfit Hna
    simp only [arm_mremap] at H
    exact check_mremap_preserves_na (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hwf := Hwf) (Hfit := Hfit) (Hna := Hna)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_clone] at H
    exact check_clone_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    simp only [arm_mmap] at H
    exact check_mmap_preserves_na (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hwf := Hwf) (Hfit := Hfit) (Hna := Hna)
  · intro i eff m m' evs H Hwf Hfit Hna
    simp only [arm_mprotect] at H
    exact check_mprotect_preserves_na (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hwf := Hwf) (Hfit := Hfit) (Hna := Hna)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_madvise] at H
    exact check_madvise_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_accept4] at H
    exact check_accept4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_wait4] at H
    exact check_wait4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_prlimit64] at H
    exact check_prlimit64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_getrandom] at H
    exact check_getrandom_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_clone3] at H
    exact check_clone3_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hwf Hfit Hna
    refine na_inv_of_m_vmmaps ?_ Hna
    simp only [arm_faccessat2] at H
    exact check_faccessat2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)

/-- The table in the membership form a lookup produces (`lookup_ca_In`). -/
theorem checked_table_preserves_na_mem : ∀ c ∈ checked_table, arm_preserves_na c :=
  forall_mem_of_forall checked_table_preserves_na

/-! ## `sys_inv` over the dispatcher -/

/-- THE CHECKER-SIDE THEOREM: an ACCEPTED syscall preserves all three
    ledger invariants.  The three components are the three walks over the
    same answer: `check_syscall_preserves_vm_wf` (`Chain.lean`),
    `check_syscall_preserves_vm_fit` (`MapsFit.lean`) and the cover below.
    An unmodelled number makes the hypothesis impossible, so no coverage
    premise is needed. -/
theorem check_syscall_preserves_sys_inv (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : CheckedTable.check_syscall i eff m = .CheckOk m' evs)
    (Hinv : sys_inv (m_vmmaps m)) : sys_inv (m_vmmaps m') := by
  obtain ⟨Hwf, Hfit, Hna⟩ := Hinv
  refine ⟨check_syscall_preserves_vm_wf i eff m m' evs H Hwf,
    check_syscall_preserves_vm_fit i eff m m' evs H Hfit, ?_⟩
  unfold CheckedTable.check_syscall at H
  unfold LinuxSem.Checks.Sys.Dispatch.check_syscall at H
  cases hlook : lookup_ca checked_table (i.in_sysno.toNat : Int) with
  | none =>
    rw [hlook] at H
    exact absurd H (by simp)
  | some c =>
    rw [hlook] at H
    exact checked_table_preserves_na_mem c (lookup_ca_In checked_table _ c hlook)
      i eff m m' evs H Hwf Hfit Hna

/-- THE SPEC-SIDE RESULT: the same statement for the RELATIONAL spec,
    through the completeness direction, so `sys_inv` is a property of
    ADMITTED syscalls and not only of the checker's answers. -/
theorem syscall_spec_preserves_sys_inv (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : Specs.syscall_spec i m (.ok eff m' evs)) (Hinv : sys_inv (m_vmmaps m)) :
    sys_inv (m_vmmaps m') :=
  check_syscall_preserves_sys_inv i eff m m' evs
    (CheckedTable.check_syscall_complete_ok i eff m m' evs H) Hinv

end LinuxSem.Checks.NoaccessOwned
