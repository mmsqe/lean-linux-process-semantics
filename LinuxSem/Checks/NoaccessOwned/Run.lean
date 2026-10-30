/-
  * LinuxSem.Checks.NoaccessOwned.Run — `sys_inv` on every configuration a
    run reaches, and so `State.noaccess_pages_owned` there.

    One transition keeps the three ledger invariants.  An instruction step
    leaves the ledgers alone (`Run.mi_account_step_model_frame`); a system
    call moves them as its spec says (`syscall_spec_preserves_sys_inv`) and
    the materialization that follows leaves them alone
    (`State.materialize_model_accesses_frame`); an exit or a kill keeps the
    spec's own post-model.  `star` then closes under induction, and
    `star_cfg` follows because a spurious-failure configuration's executions
    are executions of the unfiltered run (`Run.star_cfg_sub`).

    `sys_inv_noaccess_pages_owned` is the bridge a consumer cites: the
    whole-run invariant gives `State.noaccess_pages_owned`, which is the
    hypothesis `Mremap.mremap_fresh_avoids_noaccess` takes.  (It lives here
    rather than in `Core.lean`, whose `na_inv_noaccess_pages_owned` is the
    `na_inv` half, because only here is the whole `sys_inv` in scope.)
-/

import LinuxSem.Checks.NoaccessOwned.Arms

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Checks
open LinuxSem.Checks.VmMapsDisjoint
open LinuxSem.Checks.MapsFit
open LinuxSem.Checks.NoaccessOwned

namespace LinuxSem.Checks.NoaccessOwned

open LinuxSem.Common.RocqSpelling

/-- What a consumer cites: `sys_inv` gives `State.noaccess_pages_owned`. -/
theorem sys_inv_noaccess_pages_owned (h : VmMaps) (H : sys_inv h) :
    noaccess_pages_owned h :=
  na_inv_noaccess_pages_owned h H.2.2

/-- One transition keeps `sys_inv`. -/
theorem sstep_preserves_sys_inv (segs : List Segment) (c : config) (evs : List event)
    (c' : config) (Hstep : sstep segs c evs (.SNext c'))
    (Hinv : sys_inv (m_vmmaps c.cfg_model)) :
    sys_inv (m_vmmaps c'.cfg_model) := by
  cases Hstep with
  | instr ms model ms' model' hh hsvc hstep =>
    obtain ⟨-, hvm, -⟩ := mi_account_step_model_frame segs ms model ms' model' hstep
    exact hvm ▸ Hinv
  | syscall ms model x8 eff model' model'' evs hh hsvc hspec hh' hmat =>
    obtain ⟨-, hvm, -⟩ :=
      materialize_model_accesses_frame model' (syscall_effect_accesses eff) model'' hmat
    exact hvm ▸ syscall_spec_preserves_sys_inv (sys_input segs ms x8) model eff model' evs
      hspec Hinv
  | exit ms model x8 eff model' evs code hh hsvc hspec hh' hk =>
    exact syscall_spec_preserves_sys_inv (sys_input segs ms x8) model eff model' evs hspec Hinv
  | killed ms model x8 eff model' evs sig hh hsvc hspec hk =>
    exact syscall_spec_preserves_sys_inv (sys_input segs ms x8) model eff model' evs hspec Hinv

/-- A whole execution keeps it. -/
theorem star_preserves_sys_inv (segs : List Segment) (c : config) (tr : List event)
    (c' : config) (Hstar : star segs c tr c') (Hinv : sys_inv (m_vmmaps c.cfg_model)) :
    sys_inv (m_vmmaps c'.cfg_model) := by
  induction Hstar with
  | refl c => exact Hinv
  | step c1 evs c2 tr c3 h1 h2 ih =>
    exact ih (sstep_preserves_sys_inv segs c1 evs c2 h1 Hinv)

/-- The same under a spurious-failure configuration, whose executions are
    executions of the unfiltered run (`Run.star_cfg_sub`). -/
theorem star_cfg_preserves_sys_inv (segs : List Segment) (cfg : SpuriousCfg)
    (c : config) (tr : List event) (c' : config) (Hstar : star_cfg segs cfg c tr c')
    (Hinv : sys_inv (m_vmmaps c.cfg_model)) :
    sys_inv (m_vmmaps c'.cfg_model) :=
  star_preserves_sys_inv segs c tr c' (star_cfg_sub segs cfg c tr c' Hstar) Hinv

/-- The start of every run: `Run.init_config`'s model is `State.init_model`,
    so the base case applies. -/
theorem init_config_sys_inv (segs : List Segment) (pc : Nat) (phdrs : PhdrInfo)
    (sp brk0 mbase : word) (draw : EntryDraw) (lim : Int) (inp : ProcInput) :
    sys_inv (m_vmmaps (init_config segs pc phdrs sp brk0 mbase draw lim inp).cfg_model) := by
  unfold init_config
  exact init_model_sys_inv _ brk0 mbase sp lim inp

/-- Every configuration a run of an image reaches from its initial
    configuration satisfies `sys_inv`. -/
theorem init_config_star_sys_inv (segs : List Segment) (pc : Nat) (phdrs : PhdrInfo)
    (sp brk0 mbase : word) (draw : EntryDraw) (lim : Int) (inp : ProcInput)
    (tr : List event) (c : config)
    (Hstar : star segs (init_config segs pc phdrs sp brk0 mbase draw lim inp) tr c) :
    sys_inv (m_vmmaps c.cfg_model) :=
  star_preserves_sys_inv segs _ tr c Hstar (init_config_sys_inv segs pc phdrs sp brk0 mbase draw lim inp)

/-- The same under a spurious-failure configuration. -/
theorem init_config_star_cfg_sys_inv (segs : List Segment) (cfg : SpuriousCfg) (pc : Nat)
    (phdrs : PhdrInfo) (sp brk0 mbase : word) (draw : EntryDraw) (lim : Int)
    (inp : ProcInput) (tr : List event) (c : config)
    (Hstar : star_cfg segs cfg (init_config segs pc phdrs sp brk0 mbase draw lim inp) tr c) :
    sys_inv (m_vmmaps c.cfg_model) :=
  star_cfg_preserves_sys_inv segs cfg _ tr c Hstar
    (init_config_sys_inv segs pc phdrs sp brk0 mbase draw lim inp)

end LinuxSem.Checks.NoaccessOwned
