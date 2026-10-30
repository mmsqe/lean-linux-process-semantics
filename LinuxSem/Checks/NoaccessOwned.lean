/-
  * LinuxSem.Checks.NoaccessOwned — `State.noaccess_pages_owned` on
    every reachable state: the umbrella.

    A pure import shim (imports and comments only), the shape
    `Checks/VmMapsDisjoint.lean` has: the declarations live in the parts,
    so editing one does not re-elaborate the aggregator.

    WHAT THE PACKAGE PROVES.  `State.noaccess_pages_owned` — every protected
    byte lies on a page some live `vm_maps` entry still touches — is what
    `Mremap.mremap_fresh_avoids_noaccess` takes as its hypothesis.  It is
    NOT inductive: a `brk` shrink to a break that is not page aligned frees
    no page (`Mmap.brk_unmaps`' interval is empty) while `brk_maps_next`
    cuts the byte-granular tail out of `vm_maps`, so the grant that was the
    only witness of a protected page can vanish while the page stays
    protected.  Such a state is unreachable, and what makes it unreachable
    is the stronger `na_inv`:

    - `na_shape`: every protected entry is page aligned, a whole number of
      pages, nonempty, and ends inside the address space;
    - `na_cover`: every protected byte is owned, byte for byte, by a live
      mapping — except the brk orphan slice `[vm_brk, PAGE_ALIGN vm_brk)`,
      for which the first byte of the break's page is owned.  A shrink can
      cut the slice out; it cannot cut the page's start out as well, because
      it cuts a page-aligned range (`zone_same_page`).

    `na_inv` is carried together with `VmMapsDisjoint.vm_wf` and
    `MapsFit.vm_fit` as `sys_inv`.  The package proves `sys_inv` at
    `init_model` / `init_config`, keeps it through every modeled syscall
    (the 90-arm `checked_table` enumeration, three walks deep — one per
    invariant), carries it along a whole run (`sstep_preserves_sys_inv`,
    `star_preserves_sys_inv`, `star_cfg_preserves_sys_inv`,
    `init_config_star_sys_inv`, `init_config_star_cfg_sys_inv`), and hands
    back the consumer's predicate as `sys_inv_noaccess_pages_owned`.

    WHERE THE PIECES ARE:

    - `NoaccessOwned/Core.lean` — `owned`, `na_shape`, `na_cover`,
      `na_inv'`, `na_inv`, `sys_inv`, the page arithmetic, the `owned`
      algebra, the shape lemmas every writer's leaf applies, the two
      re-recordings `na_inv_munmap` / `na_inv_mremap`, and
      `na_inv_noaccess_pages_owned` (the `na_inv` half of the bridge);
    - `NoaccessOwned/Brk.lean` — `brk`: `brk_r_ok_cases`,
      `brk_shrink_cover`, `brk_model_next_na_inv`,
      `check_brk_preserves_na`.  This is the writer the invariant exists
      for;
    - `NoaccessOwned/Writers.lean` — `munmap`, `mprotect`, `mremap`, `mmap`:
      one walk each, the leaves being the Core shape lemmas;
    - `NoaccessOwned/Arms.lean` — `init_model_na_inv`,
      `init_model_sys_inv`, `arm_preserves_na`,
      `checked_table_preserves_na`, and the two dispatcher statements
      `check_syscall_preserves_sys_inv` / `syscall_spec_preserves_sys_inv`;
    - `NoaccessOwned/Run.lean` — `sys_inv_noaccess_pages_owned` and the
      run-level lifts.
-/

import LinuxSem.Checks.NoaccessOwned.Core
import LinuxSem.Checks.NoaccessOwned.Brk
import LinuxSem.Checks.NoaccessOwned.Writers
import LinuxSem.Checks.NoaccessOwned.Arms
import LinuxSem.Checks.NoaccessOwned.Run
