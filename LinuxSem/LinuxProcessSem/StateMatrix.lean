/-
  * LinuxProcessSem.StateMatrix — the accessor/setter rewrite matrix

  **528 lemmas**:

  | shape | count |
  | --- | ---: |
  | `m_<acc>_with_<setter>` | 489 |
  | `m_<acc>_mkModel` | 17 |
  | `m_<acc>_init_model` (incl. `vm_backing_used_init_model`) | 21 |
  | `alloc_top_init` (not an accessor) | 1 |

  Of the 489 `_with_` lemmas, 465 have `m_X m` on the right; the other 63
  lemmas of the chunk are the diagonals (`= v`, `= some v`, `= true`,
  `= []`, `= none`), the one cross-subsystem exception
  (`m_statpins_with_fs`, `= statpins_restrict v (m_statpins m)`), the
  `with_statpin` cons (`= (p, bs) :: m_statpins m`), the `if`-based
  `m_killed` diagonals (`m_killed_with_killed`, `m_killed_with_halted`),
  and the `_mkModel` / `_init_model` projections.

  WHAT THE MATRIX IS FOR.  The note carried at the end of `StateInit.lean`
  explains why these are REWRITES rather than reductions: reducing through
  them with an explicit constant list (`simp only [...]`) does not work on
  the nested `Model`, because such a list has to name every constant on the
  way from `m_fds (with_fds x m)` down to `x`, and naming them ALSO unfolds
  a bare `m_fs model` — which later steps match on literally, and then
  cannot find.  So the accessors and setters are opaque to reduction, and
  these lemmas are how a proof gets through them.  Every one is `rfl`: the
  nesting is definitional, and this only decides which shapes a proof is
  allowed to see.  They are simp lemmas, so a caller writes `simp` (or
  `simp only [m_fds_with_fds,...]`) and names no field.

  NOTES ON THE SIMP SET:

  - SIMP TAGGING.  Exactly the 510 lemmas that need the attribute
  carry it; the 18 that stay untagged (`m_*_init_model` for every
  accessor the run's input does not reach, plus
  `vm_backing_used_init_model`) are untagged because rewriting them
  everywhere normalises `m_vmmaps (init_model …)` in proofs that match
  on it unreduced — see the note below.  The three `_init_model` lemmas
  that ARE tagged are `m_killed_init_model`,
  `m_sigabrt_pending_init_model`, `m_abort_terminal_init_model`.
  - OPAQUE TO `simp`, TRANSPARENT TO `rfl`.  Every `m_*` and `with_*` is a
  `def` (see `StateLedger.lean`'s header), which `simp` already refuses
  to unfold, so nothing further has to be declared for it.
  - `alloc_top_init`'s right-hand side: `bv_unsigned sp - stack_max_size`
    is `(sp.toNat : Int) - stack_max_size` here, the same function on the
  same carrier, because the tree has no `bv_unsigned` shim — the same
  spelling `StateLedger.lean` records for `alloc_top` itself.
  `vm_backing_used` and `stack_max_size` are the definitions of the same
  names.
  - `in_stdin inp`, `in_nofile inp`, … are the record projections
  `inp.in_stdin`, `inp.in_nofile`, …, the spelling `StateInit.lean`
  uses; `in_fs inp` stays a function (it seeds `/tmp` into the image).
  Same values.
  - Every proof is `rfl`, with one mechanical exception:
  `vm_backing_used_init_model` is `by rfl` under a declaration-scoped
  `maxRecDepth` (see its note).

  TRUST BOUNDARY: this file is part of the trusted specification.
-/
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateNet
import LinuxSem.LinuxProcessSem.StateStreams
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.StateInit

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/-! ## The matrix

  One lemma per (accessor, setter) pair, in a fixed order.  The 465
    off-diagonal identity lemmas are the body of the table; the comments
    mark the rows and columns that need a word of their own. -/

@[simp] theorem m_fds_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_fds (with_fds v m) = v := rfl

@[simp] theorem m_fds_with_vmmaps (v : VmMaps) (m : Model) :
    m_fds (with_vmmaps v m) = m_fds m := rfl

@[simp] theorem m_fds_with_stdin (v : InputStream) (m : Model) :
    m_fds (with_stdin v m) = m_fds m := rfl

@[simp] theorem m_fds_with_urandom (v : InputStream) (m : Model) :
    m_fds (with_urandom v m) = m_fds m := rfl

@[simp] theorem m_fds_with_fs (v : Fs.Fs) (m : Model) :
    m_fds (with_fs v m) = m_fds m := rfl

@[simp] theorem m_fds_with_halted (v : word) (m : Model) :
    m_fds (with_halted v m) = m_fds m := rfl

@[simp] theorem m_fds_with_tid (v : word) (m : Model) :
    m_fds (with_tid v m) = m_fds m := rfl

@[simp] theorem m_fds_with_rlimit_core (v : List byte) (m : Model) :
    m_fds (with_rlimit_core v m) = m_fds m := rfl

@[simp] theorem m_fds_with_clock (v : word) (m : Model) :
    m_fds (with_clock v m) = m_fds m := rfl

@[simp] theorem m_fds_with_setsid_succeeded (m : Model) :
    m_fds (with_setsid_succeeded m) = m_fds m := rfl

@[simp] theorem m_fds_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_fds (with_pipes v m) = m_fds m := rfl

@[simp] theorem m_vmmaps_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_vmmaps (with_fds v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_vmmaps (v : VmMaps) (m : Model) :
    m_vmmaps (with_vmmaps v m) = v := rfl

@[simp] theorem m_vmmaps_with_stdin (v : InputStream) (m : Model) :
    m_vmmaps (with_stdin v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_urandom (v : InputStream) (m : Model) :
    m_vmmaps (with_urandom v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_fs (v : Fs.Fs) (m : Model) :
    m_vmmaps (with_fs v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_halted (v : word) (m : Model) :
    m_vmmaps (with_halted v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_tid (v : word) (m : Model) :
    m_vmmaps (with_tid v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_rlimit_core (v : List byte) (m : Model) :
    m_vmmaps (with_rlimit_core v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_clock (v : word) (m : Model) :
    m_vmmaps (with_clock v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_setsid_succeeded (m : Model) :
    m_vmmaps (with_setsid_succeeded m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_vmmaps (with_pipes v m) = m_vmmaps m := rfl

@[simp] theorem m_stdin_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_stdin (with_fds v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_urandom (with_fds v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_vmmaps (v : VmMaps) (m : Model) :
    m_stdin (with_vmmaps v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_vmmaps (v : VmMaps) (m : Model) :
    m_urandom (with_vmmaps v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_stdin (v : InputStream) (m : Model) :
    m_stdin (with_stdin v m) = v := rfl

@[simp] theorem m_urandom_with_stdin (v : InputStream) (m : Model) :
    m_urandom (with_stdin v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_urandom (v : InputStream) (m : Model) :
    m_stdin (with_urandom v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_urandom (v : InputStream) (m : Model) :
    m_urandom (with_urandom v m) = v := rfl

@[simp] theorem m_stdin_with_fs (v : Fs.Fs) (m : Model) :
    m_stdin (with_fs v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_fs (v : Fs.Fs) (m : Model) :
    m_urandom (with_fs v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_halted (v : word) (m : Model) :
    m_stdin (with_halted v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_halted (v : word) (m : Model) :
    m_urandom (with_halted v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_tid (v : word) (m : Model) :
    m_stdin (with_tid v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_tid (v : word) (m : Model) :
    m_urandom (with_tid v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_rlimit_core (v : List byte) (m : Model) :
    m_stdin (with_rlimit_core v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_rlimit_core (v : List byte) (m : Model) :
    m_urandom (with_rlimit_core v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_clock (v : word) (m : Model) :
    m_stdin (with_clock v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_clock (v : word) (m : Model) :
    m_urandom (with_clock v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_setsid_succeeded (m : Model) :
    m_stdin (with_setsid_succeeded m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_setsid_succeeded (m : Model) :
    m_urandom (with_setsid_succeeded m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_stdin (with_pipes v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_urandom (with_pipes v m) = m_urandom m := rfl

@[simp] theorem m_fs_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_fs (with_fds v m) = m_fs m := rfl

@[simp] theorem m_fs_with_vmmaps (v : VmMaps) (m : Model) :
    m_fs (with_vmmaps v m) = m_fs m := rfl

@[simp] theorem m_fs_with_stdin (v : InputStream) (m : Model) :
    m_fs (with_stdin v m) = m_fs m := rfl

@[simp] theorem m_fs_with_urandom (v : InputStream) (m : Model) :
    m_fs (with_urandom v m) = m_fs m := rfl

@[simp] theorem m_fs_with_fs (v : Fs.Fs) (m : Model) :
    m_fs (with_fs v m) = v := rfl

@[simp] theorem m_fs_with_halted (v : word) (m : Model) :
    m_fs (with_halted v m) = m_fs m := rfl

@[simp] theorem m_fs_with_tid (v : word) (m : Model) :
    m_fs (with_tid v m) = m_fs m := rfl

@[simp] theorem m_fs_with_rlimit_core (v : List byte) (m : Model) :
    m_fs (with_rlimit_core v m) = m_fs m := rfl

@[simp] theorem m_fs_with_clock (v : word) (m : Model) :
    m_fs (with_clock v m) = m_fs m := rfl

@[simp] theorem m_fs_with_setsid_succeeded (m : Model) :
    m_fs (with_setsid_succeeded m) = m_fs m := rfl

@[simp] theorem m_fs_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_fs (with_pipes v m) = m_fs m := rfl

@[simp] theorem m_halted_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_halted (with_fds v m) = m_halted m := rfl

@[simp] theorem m_halted_with_vmmaps (v : VmMaps) (m : Model) :
    m_halted (with_vmmaps v m) = m_halted m := rfl

@[simp] theorem m_halted_with_stdin (v : InputStream) (m : Model) :
    m_halted (with_stdin v m) = m_halted m := rfl

@[simp] theorem m_halted_with_urandom (v : InputStream) (m : Model) :
    m_halted (with_urandom v m) = m_halted m := rfl

@[simp] theorem m_halted_with_fs (v : Fs.Fs) (m : Model) :
    m_halted (with_fs v m) = m_halted m := rfl

@[simp] theorem m_halted_with_halted (v : word) (m : Model) :
    m_halted (with_halted v m) = some v := rfl

@[simp] theorem m_halted_with_tid (v : word) (m : Model) :
    m_halted (with_tid v m) = m_halted m := rfl

@[simp] theorem m_halted_with_rlimit_core (v : List byte) (m : Model) :
    m_halted (with_rlimit_core v m) = m_halted m := rfl

@[simp] theorem m_halted_with_clock (v : word) (m : Model) :
    m_halted (with_clock v m) = m_halted m := rfl

@[simp] theorem m_halted_with_setsid_succeeded (m : Model) :
    m_halted (with_setsid_succeeded m) = m_halted m := rfl

@[simp] theorem m_halted_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_halted (with_pipes v m) = m_halted m := rfl

@[simp] theorem m_tid_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_tid (with_fds v m) = m_tid m := rfl

@[simp] theorem m_tid_with_vmmaps (v : VmMaps) (m : Model) :
    m_tid (with_vmmaps v m) = m_tid m := rfl

@[simp] theorem m_tid_with_stdin (v : InputStream) (m : Model) :
    m_tid (with_stdin v m) = m_tid m := rfl

@[simp] theorem m_tid_with_urandom (v : InputStream) (m : Model) :
    m_tid (with_urandom v m) = m_tid m := rfl

@[simp] theorem m_tid_with_fs (v : Fs.Fs) (m : Model) :
    m_tid (with_fs v m) = m_tid m := rfl

@[simp] theorem m_tid_with_halted (v : word) (m : Model) :
    m_tid (with_halted v m) = m_tid m := rfl

@[simp] theorem m_tid_with_tid (v : word) (m : Model) :
    m_tid (with_tid v m) = some v := rfl

@[simp] theorem m_tid_with_rlimit_core (v : List byte) (m : Model) :
    m_tid (with_rlimit_core v m) = m_tid m := rfl

@[simp] theorem m_tid_with_clock (v : word) (m : Model) :
    m_tid (with_clock v m) = m_tid m := rfl

@[simp] theorem m_tid_with_setsid_succeeded (m : Model) :
    m_tid (with_setsid_succeeded m) = m_tid m := rfl

@[simp] theorem m_tid_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_tid (with_pipes v m) = m_tid m := rfl

@[simp] theorem m_rlimit_core_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_rlimit_core (with_fds v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_vmmaps (v : VmMaps) (m : Model) :
    m_rlimit_core (with_vmmaps v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_stdin (v : InputStream) (m : Model) :
    m_rlimit_core (with_stdin v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_urandom (v : InputStream) (m : Model) :
    m_rlimit_core (with_urandom v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_fs (v : Fs.Fs) (m : Model) :
    m_rlimit_core (with_fs v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_halted (v : word) (m : Model) :
    m_rlimit_core (with_halted v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_tid (v : word) (m : Model) :
    m_rlimit_core (with_tid v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_rlimit_core (v : List byte) (m : Model) :
    m_rlimit_core (with_rlimit_core v m) = some v := rfl

@[simp] theorem m_rlimit_core_with_clock (v : word) (m : Model) :
    m_rlimit_core (with_clock v m) = m_rlimit_core m := rfl

@[simp] theorem m_clock_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_clock (with_fds v m) = m_clock m := rfl

@[simp] theorem m_clock_with_vmmaps (v : VmMaps) (m : Model) :
    m_clock (with_vmmaps v m) = m_clock m := rfl

@[simp] theorem m_clock_with_stdin (v : InputStream) (m : Model) :
    m_clock (with_stdin v m) = m_clock m := rfl

@[simp] theorem m_clock_with_urandom (v : InputStream) (m : Model) :
    m_clock (with_urandom v m) = m_clock m := rfl

@[simp] theorem m_clock_with_fs (v : Fs.Fs) (m : Model) :
    m_clock (with_fs v m) = m_clock m := rfl

@[simp] theorem m_clock_with_halted (v : word) (m : Model) :
    m_clock (with_halted v m) = m_clock m := rfl

@[simp] theorem m_clock_with_tid (v : word) (m : Model) :
    m_clock (with_tid v m) = m_clock m := rfl

@[simp] theorem m_clock_with_rlimit_core (v : List byte) (m : Model) :
    m_clock (with_rlimit_core v m) = m_clock m := rfl

@[simp] theorem m_clock_with_setsid_succeeded (m : Model) :
    m_clock (with_setsid_succeeded m) = m_clock m := rfl

@[simp] theorem m_clock_with_clock (v : word) (m : Model) :
    m_clock (with_clock v m) = v := rfl

@[simp] theorem m_creds_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_creds (with_fds v m) = m_creds m := rfl

@[simp] theorem m_creds_with_vmmaps (v : VmMaps) (m : Model) :
    m_creds (with_vmmaps v m) = m_creds m := rfl

@[simp] theorem m_creds_with_stdin (v : InputStream) (m : Model) :
    m_creds (with_stdin v m) = m_creds m := rfl

@[simp] theorem m_creds_with_urandom (v : InputStream) (m : Model) :
    m_creds (with_urandom v m) = m_creds m := rfl

@[simp] theorem m_creds_with_fs (v : Fs.Fs) (m : Model) :
    m_creds (with_fs v m) = m_creds m := rfl

@[simp] theorem m_creds_with_halted (v : word) (m : Model) :
    m_creds (with_halted v m) = m_creds m := rfl

@[simp] theorem m_creds_with_tid (v : word) (m : Model) :
    m_creds (with_tid v m) = m_creds m := rfl

@[simp] theorem m_creds_with_rlimit_core (v : List byte) (m : Model) :
    m_creds (with_rlimit_core v m) = m_creds m := rfl

@[simp] theorem m_creds_with_clock (v : word) (m : Model) :
    m_creds (with_clock v m) = m_creds m := rfl

@[simp] theorem m_creds_with_creds (v : Creds) (m : Model) :
    m_creds (with_creds v m) = v := rfl

@[simp] theorem m_fds_with_creds (v : Creds) (m : Model) :
    m_fds (with_creds v m) = m_fds m := rfl

@[simp] theorem m_vmmaps_with_creds (v : Creds) (m : Model) :
    m_vmmaps (with_creds v m) = m_vmmaps m := rfl

@[simp] theorem m_stdin_with_creds (v : Creds) (m : Model) :
    m_stdin (with_creds v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_creds (v : Creds) (m : Model) :
    m_urandom (with_creds v m) = m_urandom m := rfl

@[simp] theorem m_fs_with_creds (v : Creds) (m : Model) :
    m_fs (with_creds v m) = m_fs m := rfl

@[simp] theorem m_halted_with_creds (v : Creds) (m : Model) :
    m_halted (with_creds v m) = m_halted m := rfl

@[simp] theorem m_tid_with_creds (v : Creds) (m : Model) :
    m_tid (with_creds v m) = m_tid m := rfl

@[simp] theorem m_rlimit_core_with_creds (v : Creds) (m : Model) :
    m_rlimit_core (with_creds v m) = m_rlimit_core m := rfl

@[simp] theorem m_clock_with_creds (v : Creds) (m : Model) :
    m_clock (with_creds v m) = m_clock m := rfl

@[simp] theorem m_net_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_net (with_fds v m) = m_net m := rfl

@[simp] theorem m_net_with_vmmaps (v : VmMaps) (m : Model) :
    m_net (with_vmmaps v m) = m_net m := rfl

@[simp] theorem m_net_with_stdin (v : InputStream) (m : Model) :
    m_net (with_stdin v m) = m_net m := rfl

@[simp] theorem m_net_with_urandom (v : InputStream) (m : Model) :
    m_net (with_urandom v m) = m_net m := rfl

@[simp] theorem m_net_with_fs (v : Fs.Fs) (m : Model) :
    m_net (with_fs v m) = m_net m := rfl

@[simp] theorem m_net_with_halted (v : word) (m : Model) :
    m_net (with_halted v m) = m_net m := rfl

@[simp] theorem m_net_with_tid (v : word) (m : Model) :
    m_net (with_tid v m) = m_net m := rfl

@[simp] theorem m_net_with_rlimit_core (v : List byte) (m : Model) :
    m_net (with_rlimit_core v m) = m_net m := rfl

@[simp] theorem m_net_with_clock (v : word) (m : Model) :
    m_net (with_clock v m) = m_net m := rfl

@[simp] theorem m_net_with_creds (v : Creds) (m : Model) :
    m_net (with_creds v m) = m_net m := rfl

@[simp] theorem m_net_with_net (v : NetQueue) (m : Model) :
    m_net (with_net v m) = v := rfl

@[simp] theorem m_conn_ix_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_conn_ix (with_fds v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_vmmaps (v : VmMaps) (m : Model) :
    m_conn_ix (with_vmmaps v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_stdin (v : InputStream) (m : Model) :
    m_conn_ix (with_stdin v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_urandom (v : InputStream) (m : Model) :
    m_conn_ix (with_urandom v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_fs (v : Fs.Fs) (m : Model) :
    m_conn_ix (with_fs v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_halted (v : word) (m : Model) :
    m_conn_ix (with_halted v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_tid (v : word) (m : Model) :
    m_conn_ix (with_tid v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_rlimit_core (v : List byte) (m : Model) :
    m_conn_ix (with_rlimit_core v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_clock (v : word) (m : Model) :
    m_conn_ix (with_clock v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_creds (v : Creds) (m : Model) :
    m_conn_ix (with_creds v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_net (v : NetQueue) (m : Model) :
    m_conn_ix (with_net v m) = m_conn_ix m := rfl

@[simp] theorem m_fds_with_net (v : NetQueue) (m : Model) :
    m_fds (with_net v m) = m_fds m := rfl

@[simp] theorem m_vmmaps_with_net (v : NetQueue) (m : Model) :
    m_vmmaps (with_net v m) = m_vmmaps m := rfl

@[simp] theorem m_stdin_with_net (v : NetQueue) (m : Model) :
    m_stdin (with_net v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_net (v : NetQueue) (m : Model) :
    m_urandom (with_net v m) = m_urandom m := rfl

@[simp] theorem m_fs_with_net (v : NetQueue) (m : Model) :
    m_fs (with_net v m) = m_fs m := rfl

@[simp] theorem m_halted_with_net (v : NetQueue) (m : Model) :
    m_halted (with_net v m) = m_halted m := rfl

@[simp] theorem m_tid_with_net (v : NetQueue) (m : Model) :
    m_tid (with_net v m) = m_tid m := rfl

@[simp] theorem m_rlimit_core_with_net (v : NetQueue) (m : Model) :
    m_rlimit_core (with_net v m) = m_rlimit_core m := rfl

@[simp] theorem m_clock_with_net (v : NetQueue) (m : Model) :
    m_clock (with_net v m) = m_clock m := rfl

@[simp] theorem m_creds_with_net (v : NetQueue) (m : Model) :
    m_creds (with_net v m) = m_creds m := rfl

@[simp] theorem m_rlimit_core_with_setsid_succeeded (m : Model) :
    m_rlimit_core (with_setsid_succeeded m) = m_rlimit_core m := rfl

@[simp] theorem m_setsid_succeeded_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_setsid_succeeded (with_fds v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_vmmaps (v : VmMaps) (m : Model) :
    m_setsid_succeeded (with_vmmaps v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_stdin (v : InputStream) (m : Model) :
    m_setsid_succeeded (with_stdin v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_urandom (v : InputStream) (m : Model) :
    m_setsid_succeeded (with_urandom v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_fs (v : Fs.Fs) (m : Model) :
    m_setsid_succeeded (with_fs v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_halted (v : word) (m : Model) :
    m_setsid_succeeded (with_halted v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_tid (v : word) (m : Model) :
    m_setsid_succeeded (with_tid v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_rlimit_core (v : List byte) (m : Model) :
    m_setsid_succeeded (with_rlimit_core v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_setsid_succeeded (m : Model) :
    m_setsid_succeeded (with_setsid_succeeded m) = true := rfl

@[simp] theorem m_setsid_succeeded_with_clock (v : word) (m : Model) :
    m_setsid_succeeded (with_clock v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_creds_with_setsid_succeeded (m : Model) :
    m_creds (with_setsid_succeeded m) = m_creds m := rfl

@[simp] theorem m_setsid_succeeded_with_creds (v : Creds) (m : Model) :
    m_setsid_succeeded (with_creds v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_net (v : NetQueue) (m : Model) :
    m_setsid_succeeded (with_net v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_net_with_setsid_succeeded (m : Model) :
    m_net (with_setsid_succeeded m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_setsid_succeeded (m : Model) :
    m_conn_ix (with_setsid_succeeded m) = m_conn_ix m := rfl

@[simp] theorem m_clock_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_clock (with_pipes v m) = m_clock m := rfl

@[simp] theorem m_pipes_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_pipes (with_fds v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_vmmaps (v : VmMaps) (m : Model) :
    m_pipes (with_vmmaps v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_stdin (v : InputStream) (m : Model) :
    m_pipes (with_stdin v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_urandom (v : InputStream) (m : Model) :
    m_pipes (with_urandom v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_fs (v : Fs.Fs) (m : Model) :
    m_pipes (with_fs v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_halted (v : word) (m : Model) :
    m_pipes (with_halted v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_tid (v : word) (m : Model) :
    m_pipes (with_tid v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_rlimit_core (v : List byte) (m : Model) :
    m_pipes (with_rlimit_core v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_clock (v : word) (m : Model) :
    m_pipes (with_clock v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_pipes (with_pipes v m) = v := rfl

@[simp] theorem m_rlimit_core_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_rlimit_core (with_pipes v m) = m_rlimit_core m := rfl

/-- The pipe table's half of the square against the other
    fields — the socket queue and its connection counter, the
    credentials, and the session bit.  [with_pipes] lives in [FdState] and
  every one of these lives elsewhere, so both directions are `rfl`;
  they are here because the simp set needs the pair, not because either
  direction is in doubt. -/

@[simp] theorem m_pipes_with_net (v : NetQueue) (m : Model) :
    m_pipes (with_net v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_creds (v : Creds) (m : Model) :
    m_pipes (with_creds v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_setsid_succeeded (m : Model) :
    m_pipes (with_setsid_succeeded m) = m_pipes m := rfl

@[simp] theorem m_net_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_net (with_pipes v m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_conn_ix (with_pipes v m) = m_conn_ix m := rfl

@[simp] theorem m_creds_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_creds (with_pipes v m) = m_creds m := rfl

@[simp] theorem m_setsid_succeeded_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_setsid_succeeded (with_pipes v m) = m_setsid_succeeded m := rfl

/-- The blocked mask against the other setters and accessors.  Every one
  is `rfl`: [with_sigmask] rebuilds [ProcState] alone, and every
    other setter either passes [m_proc m] through or carries
    [m_sigmask m] across explicitly. -/

@[simp] theorem m_sigmask_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_sigmask (with_fds v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_vmmaps (v : VmMaps) (m : Model) :
    m_sigmask (with_vmmaps v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_vm_backing (l : List (word × word)) (mt : List word)
    (m : Model) :
    m_sigmask (with_vm_backing l mt m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_stdin (v : InputStream) (m : Model) :
    m_sigmask (with_stdin v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_urandom (v : InputStream) (m : Model) :
    m_sigmask (with_urandom v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_net (v : NetQueue) (m : Model) :
    m_sigmask (with_net v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_fs (v : Fs.Fs) (m : Model) :
    m_sigmask (with_fs v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_halted (v : word) (m : Model) :
    m_sigmask (with_halted v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_tid (v : word) (m : Model) :
    m_sigmask (with_tid v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_rlimit_core (v : List byte) (m : Model) :
    m_sigmask (with_rlimit_core v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_creds (v : Creds) (m : Model) :
    m_sigmask (with_creds v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_setsid_succeeded (m : Model) :
    m_sigmask (with_setsid_succeeded m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_children (m : Model) :
    m_sigmask (with_children m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_clock (v : word) (m : Model) :
    m_sigmask (with_clock v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_sigmask (with_accepted v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_sigmask (v : word) (m : Model) :
    m_sigmask (with_sigmask v m) = v := rfl

@[simp] theorem m_fds_with_sigmask (v : word) (m : Model) :
    m_fds (with_sigmask v m) = m_fds m := rfl

@[simp] theorem m_vmmaps_with_sigmask (v : word) (m : Model) :
    m_vmmaps (with_sigmask v m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_with_sigmask (v : word) (m : Model) :
    m_vm_lazy (with_sigmask v m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_materialized_with_sigmask (v : word) (m : Model) :
    m_vm_materialized (with_sigmask v m) = m_vm_materialized m := rfl

@[simp] theorem m_stdin_with_sigmask (v : word) (m : Model) :
    m_stdin (with_sigmask v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_sigmask (v : word) (m : Model) :
    m_urandom (with_sigmask v m) = m_urandom m := rfl

@[simp] theorem m_net_with_sigmask (v : word) (m : Model) :
    m_net (with_sigmask v m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_sigmask (v : word) (m : Model) :
    m_conn_ix (with_sigmask v m) = m_conn_ix m := rfl

@[simp] theorem m_fs_with_sigmask (v : word) (m : Model) :
    m_fs (with_sigmask v m) = m_fs m := rfl

@[simp] theorem m_halted_with_sigmask (v : word) (m : Model) :
    m_halted (with_sigmask v m) = m_halted m := rfl

@[simp] theorem m_tid_with_sigmask (v : word) (m : Model) :
    m_tid (with_sigmask v m) = m_tid m := rfl

@[simp] theorem m_setsid_succeeded_with_sigmask (v : word) (m : Model) :
    m_setsid_succeeded (with_sigmask v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_has_children_with_sigmask (v : word) (m : Model) :
    m_has_children (with_sigmask v m) = m_has_children m := rfl

@[simp] theorem m_rlimit_core_with_sigmask (v : word) (m : Model) :
    m_rlimit_core (with_sigmask v m) = m_rlimit_core m := rfl

@[simp] theorem m_clock_with_sigmask (v : word) (m : Model) :
    m_clock (with_sigmask v m) = m_clock m := rfl

@[simp] theorem m_creds_with_sigmask (v : word) (m : Model) :
    m_creds (with_sigmask v m) = m_creds m := rfl

/-- The alternate-signal-stack bit's row and column of the table above.
    The row says every other setter carries it across, which is the
    property [with_sigaltstack_installed]'s own note calls load-bearing; the
    column says installing it moves nothing else. -/

@[simp] theorem m_sigaltstack_installed_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_sigaltstack_installed (with_fds v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_sigaltstack_installed (with_pipes v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_vmmaps (v : VmMaps) (m : Model) :
    m_sigaltstack_installed (with_vmmaps v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_vm_backing (l : List (word × word))
    (mt : List word) (m : Model) :
    m_sigaltstack_installed (with_vm_backing l mt m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_stdin (v : InputStream) (m : Model) :
    m_sigaltstack_installed (with_stdin v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_urandom (v : InputStream) (m : Model) :
    m_sigaltstack_installed (with_urandom v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_net (v : NetQueue) (m : Model) :
    m_sigaltstack_installed (with_net v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_fs (v : Fs.Fs) (m : Model) :
    m_sigaltstack_installed (with_fs v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_halted (v : word) (m : Model) :
    m_sigaltstack_installed (with_halted v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_tid (v : word) (m : Model) :
    m_sigaltstack_installed (with_tid v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_rlimit_core (v : List byte) (m : Model) :
    m_sigaltstack_installed (with_rlimit_core v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_nofile (v : word) (m : Model) :
    m_sigaltstack_installed (with_nofile v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_creds (v : Creds) (m : Model) :
    m_sigaltstack_installed (with_creds v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_setsid_succeeded (m : Model) :
    m_sigaltstack_installed (with_setsid_succeeded m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_children (m : Model) :
    m_sigaltstack_installed (with_children m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_sigmask (v : word) (m : Model) :
    m_sigaltstack_installed (with_sigmask v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_clock (v : word) (m : Model) :
    m_sigaltstack_installed (with_clock v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_sigaltstack_installed (with_accepted v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_utsname (v : List byte) (m : Model) :
    m_sigaltstack_installed (with_utsname v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_sigaltstack_installed (m : Model) :
    m_sigaltstack_installed (with_sigaltstack_installed m) = true := rfl

@[simp] theorem m_fds_with_sigaltstack_installed (m : Model) :
    m_fds (with_sigaltstack_installed m) = m_fds m := rfl

@[simp] theorem m_pipes_with_sigaltstack_installed (m : Model) :
    m_pipes (with_sigaltstack_installed m) = m_pipes m := rfl

@[simp] theorem m_vmmaps_with_sigaltstack_installed (m : Model) :
    m_vmmaps (with_sigaltstack_installed m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_with_sigaltstack_installed (m : Model) :
    m_vm_lazy (with_sigaltstack_installed m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_materialized_with_sigaltstack_installed (m : Model) :
    m_vm_materialized (with_sigaltstack_installed m) = m_vm_materialized m := rfl

@[simp] theorem m_stdin_with_sigaltstack_installed (m : Model) :
    m_stdin (with_sigaltstack_installed m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_sigaltstack_installed (m : Model) :
    m_urandom (with_sigaltstack_installed m) = m_urandom m := rfl

@[simp] theorem m_net_with_sigaltstack_installed (m : Model) :
    m_net (with_sigaltstack_installed m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_sigaltstack_installed (m : Model) :
    m_conn_ix (with_sigaltstack_installed m) = m_conn_ix m := rfl

@[simp] theorem m_fs_with_sigaltstack_installed (m : Model) :
    m_fs (with_sigaltstack_installed m) = m_fs m := rfl

@[simp] theorem m_halted_with_sigaltstack_installed (m : Model) :
    m_halted (with_sigaltstack_installed m) = m_halted m := rfl

@[simp] theorem m_tid_with_sigaltstack_installed (m : Model) :
    m_tid (with_sigaltstack_installed m) = m_tid m := rfl

@[simp] theorem m_setsid_succeeded_with_sigaltstack_installed (m : Model) :
    m_setsid_succeeded (with_sigaltstack_installed m) = m_setsid_succeeded m := rfl

@[simp] theorem m_has_children_with_sigaltstack_installed (m : Model) :
    m_has_children (with_sigaltstack_installed m) = m_has_children m := rfl

@[simp] theorem m_sigmask_with_sigaltstack_installed (m : Model) :
    m_sigmask (with_sigaltstack_installed m) = m_sigmask m := rfl

@[simp] theorem m_rlimit_core_with_sigaltstack_installed (m : Model) :
    m_rlimit_core (with_sigaltstack_installed m) = m_rlimit_core m := rfl

@[simp] theorem m_nofile_with_sigaltstack_installed (m : Model) :
    m_nofile (with_sigaltstack_installed m) = m_nofile m := rfl

@[simp] theorem m_clock_with_sigaltstack_installed (m : Model) :
    m_clock (with_sigaltstack_installed m) = m_clock m := rfl

@[simp] theorem m_creds_with_sigaltstack_installed (m : Model) :
    m_creds (with_sigaltstack_installed m) = m_creds m := rfl

/- And the accessors of a freshly built model. -/

/-- The soft descriptor limit's row and column of the table above.
    [with_nofile] runs once, in [init_model], so the column exists for the
    accessors that read a model built by it; the row is what a proof about
    [Sys.Fs.File.dup3_spec] needs, since installing a descriptor rewrites
    the fd table and the limit has to survive that. -/

@[simp] theorem m_nofile_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_nofile (with_fds v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_vmmaps (v : VmMaps) (m : Model) :
    m_nofile (with_vmmaps v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_stdin (v : InputStream) (m : Model) :
    m_nofile (with_stdin v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_urandom (v : InputStream) (m : Model) :
    m_nofile (with_urandom v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_fs (v : Fs.Fs) (m : Model) :
    m_nofile (with_fs v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_halted (v : word) (m : Model) :
    m_nofile (with_halted v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_tid (v : word) (m : Model) :
    m_nofile (with_tid v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_rlimit_core (v : List byte) (m : Model) :
    m_nofile (with_rlimit_core v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_clock (v : word) (m : Model) :
    m_nofile (with_clock v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_creds (v : Creds) (m : Model) :
    m_nofile (with_creds v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_net (v : NetQueue) (m : Model) :
    m_nofile (with_net v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_setsid_succeeded (m : Model) :
    m_nofile (with_setsid_succeeded m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_nofile (v : word) (m : Model) :
    m_nofile (with_nofile v m) = v := rfl

@[simp] theorem m_fds_with_nofile (v : word) (m : Model) :
    m_fds (with_nofile v m) = m_fds m := rfl

@[simp] theorem m_vmmaps_with_nofile (v : word) (m : Model) :
    m_vmmaps (with_nofile v m) = m_vmmaps m := rfl

@[simp] theorem m_stdin_with_nofile (v : word) (m : Model) :
    m_stdin (with_nofile v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_nofile (v : word) (m : Model) :
    m_urandom (with_nofile v m) = m_urandom m := rfl

@[simp] theorem m_fs_with_nofile (v : word) (m : Model) :
    m_fs (with_nofile v m) = m_fs m := rfl

@[simp] theorem m_halted_with_nofile (v : word) (m : Model) :
    m_halted (with_nofile v m) = m_halted m := rfl

@[simp] theorem m_tid_with_nofile (v : word) (m : Model) :
    m_tid (with_nofile v m) = m_tid m := rfl

@[simp] theorem m_rlimit_core_with_nofile (v : word) (m : Model) :
    m_rlimit_core (with_nofile v m) = m_rlimit_core m := rfl

@[simp] theorem m_clock_with_nofile (v : word) (m : Model) :
    m_clock (with_nofile v m) = m_clock m := rfl

@[simp] theorem m_creds_with_nofile (v : word) (m : Model) :
    m_creds (with_nofile v m) = m_creds m := rfl

@[simp] theorem m_net_with_nofile (v : word) (m : Model) :
    m_net (with_nofile v m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_nofile (v : word) (m : Model) :
    m_conn_ix (with_nofile v m) = m_conn_ix m := rfl

@[simp] theorem m_setsid_succeeded_with_nofile (v : word) (m : Model) :
    m_setsid_succeeded (with_nofile v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_fds_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_fds (mkModel fds vm stdin fs halted tid rlim) = fds := rfl

@[simp] theorem m_vmmaps_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_vmmaps (mkModel fds vm stdin fs halted tid rlim) = vm := rfl

@[simp] theorem m_stdin_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_stdin (mkModel fds vm stdin fs halted tid rlim) = stdin := rfl

@[simp] theorem m_fs_mkModel (fds : List (word × FdEntry)) (vm : VmMaps) (stdin : InputStream)
    (fs : Fs.Fs) (halted : Option word) (tid : Option word) (rlim : Option (List byte)) :
    m_fs (mkModel fds vm stdin fs halted tid rlim) = fs := rfl

@[simp] theorem m_halted_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_halted (mkModel fds vm stdin fs halted tid rlim) = halted := rfl

@[simp] theorem m_tid_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_tid (mkModel fds vm stdin fs halted tid rlim) = tid := rfl

@[simp] theorem m_rlimit_core_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_rlimit_core (mkModel fds vm stdin fs halted tid rlim) = rlim := rfl

@[simp] theorem m_nofile_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_nofile (mkModel fds vm stdin fs halted tid rlim) = default_nofile := rfl

@[simp] theorem m_clock_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_clock (mkModel fds vm stdin fs halted tid rlim) = BitVec.ofInt 64 0 := rfl

/-- A model built without a [ProcInput] runs as nobody; see [overflow_id]. -/

@[simp] theorem m_net_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_net (mkModel fds vm stdin fs halted tid rlim) = net_silent := rfl

@[simp] theorem m_conn_ix_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_conn_ix (mkModel fds vm stdin fs halted tid rlim) = BitVec.ofInt 64 0 := rfl

@[simp] theorem m_creds_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_creds (mkModel fds vm stdin fs halted tid rlim) =
      Creds.mkCreds overflow_id overflow_id overflow_id overflow_id overflow_id
        overflow_id [] := rfl

/-- A freshly built model has led no session: [mkModel] defaults the bit, as
    it defaults the sparse VM ledgers, so no call site passes it. -/

@[simp] theorem m_sigmask_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_sigmask (mkModel fds vm stdin fs halted tid rlim) = BitVec.ofInt 64 0 := rfl

@[simp] theorem m_setsid_succeeded_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_setsid_succeeded (mkModel fds vm stdin fs halted tid rlim) = false := rfl

@[simp] theorem m_pipes_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_pipes (mkModel fds vm stdin fs halted tid rlim) = [] := rfl

/-- The UTS-name pin against every other move of the model.  One row and
    one column of the matrix above: nothing else reads or writes it, so
    every entry but the diagonal one is [m_utsname m]. -/

@[simp] theorem m_utsname_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_utsname (with_fds v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_utsname (with_pipes v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_vmmaps (v : VmMaps) (m : Model) :
    m_utsname (with_vmmaps v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_vm_backing (lz : List (word × word)) (mz : List word)
    (m : Model) :
    m_utsname (with_vm_backing lz mz m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_stdin (v : InputStream) (m : Model) :
    m_utsname (with_stdin v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_urandom (v : InputStream) (m : Model) :
    m_utsname (with_urandom v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_net (v : NetQueue) (m : Model) :
    m_utsname (with_net v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_utsname (with_accepted v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_fs (v : Fs.Fs) (m : Model) :
    m_utsname (with_fs v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_halted (v : word) (m : Model) :
    m_utsname (with_halted v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_tid (v : word) (m : Model) :
    m_utsname (with_tid v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_rlimit_core (v : List byte) (m : Model) :
    m_utsname (with_rlimit_core v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_nofile (v : word) (m : Model) :
    m_utsname (with_nofile v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_creds (v : Creds) (m : Model) :
    m_utsname (with_creds v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_setsid_succeeded (m : Model) :
    m_utsname (with_setsid_succeeded m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_children (m : Model) :
    m_utsname (with_children m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_sigmask (v : word) (m : Model) :
    m_utsname (with_sigmask v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_clock (v : word) (m : Model) :
    m_utsname (with_clock v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_sigaltstack_installed (m : Model) :
    m_utsname (with_sigaltstack_installed m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_utsname (v : List byte) (m : Model) :
    m_utsname (with_utsname v m) = some v := rfl

@[simp] theorem m_fds_with_utsname (v : List byte) (m : Model) :
    m_fds (with_utsname v m) = m_fds m := rfl

@[simp] theorem m_pipes_with_utsname (v : List byte) (m : Model) :
    m_pipes (with_utsname v m) = m_pipes m := rfl

@[simp] theorem m_vmmaps_with_utsname (v : List byte) (m : Model) :
    m_vmmaps (with_utsname v m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_with_utsname (v : List byte) (m : Model) :
    m_vm_lazy (with_utsname v m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_materialized_with_utsname (v : List byte) (m : Model) :
    m_vm_materialized (with_utsname v m) = m_vm_materialized m := rfl

@[simp] theorem m_stdin_with_utsname (v : List byte) (m : Model) :
    m_stdin (with_utsname v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_utsname (v : List byte) (m : Model) :
    m_urandom (with_utsname v m) = m_urandom m := rfl

@[simp] theorem m_net_with_utsname (v : List byte) (m : Model) :
    m_net (with_utsname v m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_utsname (v : List byte) (m : Model) :
    m_conn_ix (with_utsname v m) = m_conn_ix m := rfl

@[simp] theorem m_fs_with_utsname (v : List byte) (m : Model) :
    m_fs (with_utsname v m) = m_fs m := rfl

@[simp] theorem m_halted_with_utsname (v : List byte) (m : Model) :
    m_halted (with_utsname v m) = m_halted m := rfl

@[simp] theorem m_tid_with_utsname (v : List byte) (m : Model) :
    m_tid (with_utsname v m) = m_tid m := rfl

@[simp] theorem m_setsid_succeeded_with_utsname (v : List byte) (m : Model) :
    m_setsid_succeeded (with_utsname v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_has_children_with_utsname (v : List byte) (m : Model) :
    m_has_children (with_utsname v m) = m_has_children m := rfl

@[simp] theorem m_sigmask_with_utsname (v : List byte) (m : Model) :
    m_sigmask (with_utsname v m) = m_sigmask m := rfl

@[simp] theorem m_rlimit_core_with_utsname (v : List byte) (m : Model) :
    m_rlimit_core (with_utsname v m) = m_rlimit_core m := rfl

@[simp] theorem m_nofile_with_utsname (v : List byte) (m : Model) :
    m_nofile (with_utsname v m) = m_nofile m := rfl

@[simp] theorem m_clock_with_utsname (v : List byte) (m : Model) :
    m_clock (with_utsname v m) = m_clock m := rfl

@[simp] theorem m_creds_with_utsname (v : List byte) (m : Model) :
    m_creds (with_utsname v m) = m_creds m := rfl

@[simp] theorem m_utsname_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_utsname (mkModel fds vm stdin fs halted tid rlim) = none := rfl

/-- The per-file stat pins against every other move of the model.  One
    row and one column of the matrix above: [Fs.Stat.fstat_spec] is the
    only reader and [with_statpin] the only writer, so every entry but
    the diagonal one is [m_statpins m].

    The column is what the framing obligations need.  A [fstat] that
    creates a pin changes the model on a
    SUCCESS that also writes user memory, so
    [Checks.VmMapsDisjoint]'s per-arm frame lemma for 80 has to
  see through [with_statpin] to the untouched [m_vmmaps]; that lemma is
    `Checks.VmMapsDisjoint.check_fstat_frame` in
    `Checks/VmMapsDisjoint/Frames.lean`, so the rewrite lemmas this file
    supplies do have a consumer.  They are still stated here rather than
    there because this file owns the [m_statpins] column. -/

@[simp] theorem m_statpins_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_statpins (with_fds v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_statpins (with_pipes v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_vmmaps (v : VmMaps) (m : Model) :
    m_statpins (with_vmmaps v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_vm_backing (lz : List (word × word)) (mz : List word)
    (m : Model) :
    m_statpins (with_vm_backing lz mz m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_stdin (v : InputStream) (m : Model) :
    m_statpins (with_stdin v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_urandom (v : InputStream) (m : Model) :
    m_statpins (with_urandom v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_net (v : NetQueue) (m : Model) :
    m_statpins (with_net v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_statpins (with_accepted v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_fs (v : Fs.Fs) (m : Model) :
    m_statpins (with_fs v m) = statpins_restrict v (m_statpins m) := rfl

@[simp] theorem m_statpins_with_halted (v : word) (m : Model) :
    m_statpins (with_halted v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_tid (v : word) (m : Model) :
    m_statpins (with_tid v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_rlimit_core (v : List byte) (m : Model) :
    m_statpins (with_rlimit_core v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_nofile (v : word) (m : Model) :
    m_statpins (with_nofile v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_creds (v : Creds) (m : Model) :
    m_statpins (with_creds v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_setsid_succeeded (m : Model) :
    m_statpins (with_setsid_succeeded m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_children (m : Model) :
    m_statpins (with_children m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_sigmask (v : word) (m : Model) :
    m_statpins (with_sigmask v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_clock (v : word) (m : Model) :
    m_statpins (with_clock v m) = m_statpins m := rfl

@[simp] theorem m_statpins_with_utsname (v : List byte) (m : Model) :
    m_statpins (with_utsname v m) = m_statpins m := rfl

@[simp] theorem m_fds_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_fds (with_statpin p bs m) = m_fds m := rfl

@[simp] theorem m_pipes_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_pipes (with_statpin p bs m) = m_pipes m := rfl

@[simp] theorem m_vmmaps_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_vmmaps (with_statpin p bs m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_vm_lazy (with_statpin p bs m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_materialized_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_vm_materialized (with_statpin p bs m) = m_vm_materialized m := rfl

@[simp] theorem m_stdin_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_stdin (with_statpin p bs m) = m_stdin m := rfl

@[simp] theorem m_net_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_net (with_statpin p bs m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_conn_ix (with_statpin p bs m) = m_conn_ix m := rfl

@[simp] theorem m_fs_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_fs (with_statpin p bs m) = m_fs m := rfl

@[simp] theorem m_halted_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_halted (with_statpin p bs m) = m_halted m := rfl

@[simp] theorem m_tid_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_tid (with_statpin p bs m) = m_tid m := rfl

@[simp] theorem m_setsid_succeeded_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_setsid_succeeded (with_statpin p bs m) = m_setsid_succeeded m := rfl

@[simp] theorem m_has_children_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_has_children (with_statpin p bs m) = m_has_children m := rfl

@[simp] theorem m_sigmask_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_sigmask (with_statpin p bs m) = m_sigmask m := rfl

@[simp] theorem m_utsname_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_utsname (with_statpin p bs m) = m_utsname m := rfl

@[simp] theorem m_rlimit_core_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_rlimit_core (with_statpin p bs m) = m_rlimit_core m := rfl

@[simp] theorem m_nofile_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_nofile (with_statpin p bs m) = m_nofile m := rfl

@[simp] theorem m_clock_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_clock (with_statpin p bs m) = m_clock m := rfl

@[simp] theorem m_creds_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_creds (with_statpin p bs m) = m_creds m := rfl

@[simp] theorem m_statpins_with_statpin (p : Fs.path) (bs : List byte) (m : Model) :
    m_statpins (with_statpin p bs m) = (p, bs) :: m_statpins m := rfl

@[simp] theorem m_statpins_mkModel (fds : List (word × FdEntry)) (vm : VmMaps)
    (stdin : InputStream) (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_statpins (mkModel fds vm stdin fs halted tid rlim) = [] := rfl

/- Opaque to reduction, on purpose.  `simp` must not walk into the
    nesting: a proof that wants past an accessor uses the rewrites above,
    which keeps [m_fs model] looking like [m_fs model] wherever it is not
    applied to a setter. -/

-- The accessors and setters are deliberately opaque to reduction: naming
-- them would let `simp` walk into the nesting, and the rewrites above are
-- how a proof gets past an accessor instead.  `m_*` and `with_*` are
-- `def`s (see `StateLedger.lean`'s header), which `simp` already refuses
-- to unfold, so the effect is built in.  Why the nesting must stay folded
-- is carried at the end of `StateInit.lean`.

/- And of the model a run starts from.  [init_model] builds one with
  [mkModel], so these are `rfl` too -- but a proof cannot see that
  through an opaque accessor, and no simp set that unfolds a list of
  constants will unfold [init_model] to show it.

  DELIBERATELY NOT in the simp set.  Rewriting these everywhere
    normalises [m_vmmaps (init_model ...)] in proofs that match on it
  unreduced, and breaks more than it fixes -- the same trap as widening
  a `simp only [...]` list.  A site that wants one names it. -/

/-- The three fields the abort path added, against every setter, and
    every other field against the three setters that write them.  Same
  shape and same `rfl` as the block above, and the same reason
    for existing -- but these carry a second job.  [procst_killed],
    [procst_sigabrt_pending] and [procst_abort_terminal] are the fields a
    run with the declaration OFF must never see move, and the lemmas
    below are what says no setter moves them: the only writers are
    [with_killed], [with_sigabrt_pending] and [with_abort_terminal], and
    every other setter carries all three across.  See
    [Kernel.Signal.tkill_spec] for the callers. -/

@[simp] theorem m_fds_with_abort_terminal (v : Bool) (m : Model) :
    m_fds (with_abort_terminal v m) = m_fds m := rfl

@[simp] theorem m_fds_with_sigabrt_pending (m : Model) :
    m_fds (with_sigabrt_pending m) = m_fds m := rfl

@[simp] theorem m_fds_with_killed (v : word) (m : Model) :
    m_fds (with_killed v m) = m_fds m := rfl

@[simp] theorem m_pipes_with_abort_terminal (v : Bool) (m : Model) :
    m_pipes (with_abort_terminal v m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_sigabrt_pending (m : Model) :
    m_pipes (with_sigabrt_pending m) = m_pipes m := rfl

@[simp] theorem m_pipes_with_killed (v : word) (m : Model) :
    m_pipes (with_killed v m) = m_pipes m := rfl

@[simp] theorem m_vmmaps_with_abort_terminal (v : Bool) (m : Model) :
    m_vmmaps (with_abort_terminal v m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_sigabrt_pending (m : Model) :
    m_vmmaps (with_sigabrt_pending m) = m_vmmaps m := rfl

@[simp] theorem m_vmmaps_with_killed (v : word) (m : Model) :
    m_vmmaps (with_killed v m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_with_abort_terminal (v : Bool) (m : Model) :
    m_vm_lazy (with_abort_terminal v m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_lazy_with_sigabrt_pending (m : Model) :
    m_vm_lazy (with_sigabrt_pending m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_lazy_with_killed (v : word) (m : Model) :
    m_vm_lazy (with_killed v m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_materialized_with_abort_terminal (v : Bool) (m : Model) :
    m_vm_materialized (with_abort_terminal v m) = m_vm_materialized m := rfl

@[simp] theorem m_vm_materialized_with_sigabrt_pending (m : Model) :
    m_vm_materialized (with_sigabrt_pending m) = m_vm_materialized m := rfl

@[simp] theorem m_vm_materialized_with_killed (v : word) (m : Model) :
    m_vm_materialized (with_killed v m) = m_vm_materialized m := rfl

@[simp] theorem m_stdin_with_abort_terminal (v : Bool) (m : Model) :
    m_stdin (with_abort_terminal v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_abort_terminal (v : Bool) (m : Model) :
    m_urandom (with_abort_terminal v m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_sigabrt_pending (m : Model) :
    m_stdin (with_sigabrt_pending m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_sigabrt_pending (m : Model) :
    m_urandom (with_sigabrt_pending m) = m_urandom m := rfl

@[simp] theorem m_stdin_with_killed (v : word) (m : Model) :
    m_stdin (with_killed v m) = m_stdin m := rfl

@[simp] theorem m_urandom_with_killed (v : word) (m : Model) :
    m_urandom (with_killed v m) = m_urandom m := rfl

@[simp] theorem m_net_with_abort_terminal (v : Bool) (m : Model) :
    m_net (with_abort_terminal v m) = m_net m := rfl

@[simp] theorem m_net_with_sigabrt_pending (m : Model) :
    m_net (with_sigabrt_pending m) = m_net m := rfl

@[simp] theorem m_net_with_killed (v : word) (m : Model) :
    m_net (with_killed v m) = m_net m := rfl

@[simp] theorem m_conn_ix_with_abort_terminal (v : Bool) (m : Model) :
    m_conn_ix (with_abort_terminal v m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_sigabrt_pending (m : Model) :
    m_conn_ix (with_sigabrt_pending m) = m_conn_ix m := rfl

@[simp] theorem m_conn_ix_with_killed (v : word) (m : Model) :
    m_conn_ix (with_killed v m) = m_conn_ix m := rfl

@[simp] theorem m_fs_with_abort_terminal (v : Bool) (m : Model) :
    m_fs (with_abort_terminal v m) = m_fs m := rfl

@[simp] theorem m_fs_with_sigabrt_pending (m : Model) :
    m_fs (with_sigabrt_pending m) = m_fs m := rfl

@[simp] theorem m_fs_with_killed (v : word) (m : Model) :
    m_fs (with_killed v m) = m_fs m := rfl

@[simp] theorem m_halted_with_abort_terminal (v : Bool) (m : Model) :
    m_halted (with_abort_terminal v m) = m_halted m := rfl

@[simp] theorem m_halted_with_sigabrt_pending (m : Model) :
    m_halted (with_sigabrt_pending m) = m_halted m := rfl

@[simp] theorem m_halted_with_killed (v : word) (m : Model) :
    m_halted (with_killed v m) = some v := rfl

@[simp] theorem m_tid_with_abort_terminal (v : Bool) (m : Model) :
    m_tid (with_abort_terminal v m) = m_tid m := rfl

@[simp] theorem m_tid_with_sigabrt_pending (m : Model) :
    m_tid (with_sigabrt_pending m) = m_tid m := rfl

@[simp] theorem m_tid_with_killed (v : word) (m : Model) :
    m_tid (with_killed v m) = m_tid m := rfl

@[simp] theorem m_setsid_succeeded_with_abort_terminal (v : Bool) (m : Model) :
    m_setsid_succeeded (with_abort_terminal v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_sigabrt_pending (m : Model) :
    m_setsid_succeeded (with_sigabrt_pending m) = m_setsid_succeeded m := rfl

@[simp] theorem m_setsid_succeeded_with_killed (v : word) (m : Model) :
    m_setsid_succeeded (with_killed v m) = m_setsid_succeeded m := rfl

@[simp] theorem m_has_children_with_abort_terminal (v : Bool) (m : Model) :
    m_has_children (with_abort_terminal v m) = m_has_children m := rfl

@[simp] theorem m_has_children_with_sigabrt_pending (m : Model) :
    m_has_children (with_sigabrt_pending m) = m_has_children m := rfl

@[simp] theorem m_has_children_with_killed (v : word) (m : Model) :
    m_has_children (with_killed v m) = m_has_children m := rfl

@[simp] theorem m_sigmask_with_abort_terminal (v : Bool) (m : Model) :
    m_sigmask (with_abort_terminal v m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_sigabrt_pending (m : Model) :
    m_sigmask (with_sigabrt_pending m) = m_sigmask m := rfl

@[simp] theorem m_sigmask_with_killed (v : word) (m : Model) :
    m_sigmask (with_killed v m) = m_sigmask m := rfl

@[simp] theorem m_utsname_with_abort_terminal (v : Bool) (m : Model) :
    m_utsname (with_abort_terminal v m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_sigabrt_pending (m : Model) :
    m_utsname (with_sigabrt_pending m) = m_utsname m := rfl

@[simp] theorem m_utsname_with_killed (v : word) (m : Model) :
    m_utsname (with_killed v m) = m_utsname m := rfl

@[simp] theorem m_rlimit_core_with_abort_terminal (v : Bool) (m : Model) :
    m_rlimit_core (with_abort_terminal v m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_sigabrt_pending (m : Model) :
    m_rlimit_core (with_sigabrt_pending m) = m_rlimit_core m := rfl

@[simp] theorem m_rlimit_core_with_killed (v : word) (m : Model) :
    m_rlimit_core (with_killed v m) = m_rlimit_core m := rfl

@[simp] theorem m_nofile_with_abort_terminal (v : Bool) (m : Model) :
    m_nofile (with_abort_terminal v m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_sigabrt_pending (m : Model) :
    m_nofile (with_sigabrt_pending m) = m_nofile m := rfl

@[simp] theorem m_nofile_with_killed (v : word) (m : Model) :
    m_nofile (with_killed v m) = m_nofile m := rfl

@[simp] theorem m_clock_with_abort_terminal (v : Bool) (m : Model) :
    m_clock (with_abort_terminal v m) = m_clock m := rfl

@[simp] theorem m_clock_with_sigabrt_pending (m : Model) :
    m_clock (with_sigabrt_pending m) = m_clock m := rfl

@[simp] theorem m_clock_with_killed (v : word) (m : Model) :
    m_clock (with_killed v m) = m_clock m := rfl

@[simp] theorem m_creds_with_abort_terminal (v : Bool) (m : Model) :
    m_creds (with_abort_terminal v m) = m_creds m := rfl

@[simp] theorem m_creds_with_sigabrt_pending (m : Model) :
    m_creds (with_sigabrt_pending m) = m_creds m := rfl

@[simp] theorem m_creds_with_killed (v : word) (m : Model) :
    m_creds (with_killed v m) = m_creds m := rfl

@[simp] theorem m_killed_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_killed (with_fds v m) = m_killed m := rfl

@[simp] theorem m_killed_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_killed (with_pipes v m) = m_killed m := rfl

@[simp] theorem m_killed_with_vmmaps (v : VmMaps) (m : Model) :
    m_killed (with_vmmaps v m) = m_killed m := rfl

@[simp] theorem m_killed_with_vm_backing (lz : List (word × word)) (mt : List word)
    (m : Model) :
    m_killed (with_vm_backing lz mt m) = m_killed m := rfl

@[simp] theorem m_killed_with_stdin (v : InputStream) (m : Model) :
    m_killed (with_stdin v m) = m_killed m := rfl

@[simp] theorem m_killed_with_urandom (v : InputStream) (m : Model) :
    m_killed (with_urandom v m) = m_killed m := rfl

@[simp] theorem m_killed_with_net (v : NetQueue) (m : Model) :
    m_killed (with_net v m) = m_killed m := rfl

@[simp] theorem m_killed_with_fs (v : Fs.Fs) (m : Model) :
    m_killed (with_fs v m) = m_killed m := rfl

@[simp] theorem m_killed_with_halted (v : word) (m : Model) :
    m_killed (with_halted v m) = none := rfl

@[simp] theorem m_killed_with_tid (v : word) (m : Model) :
    m_killed (with_tid v m) = m_killed m := rfl

@[simp] theorem m_killed_with_rlimit_core (v : List byte) (m : Model) :
    m_killed (with_rlimit_core v m) = m_killed m := rfl

@[simp] theorem m_killed_with_utsname (v : List byte) (m : Model) :
    m_killed (with_utsname v m) = m_killed m := rfl

@[simp] theorem m_killed_with_nofile (v : word) (m : Model) :
    m_killed (with_nofile v m) = m_killed m := rfl

@[simp] theorem m_killed_with_creds (v : Creds) (m : Model) :
    m_killed (with_creds v m) = m_killed m := rfl

@[simp] theorem m_killed_with_setsid_succeeded (m : Model) :
    m_killed (with_setsid_succeeded m) = m_killed m := rfl

@[simp] theorem m_killed_with_children (m : Model) :
    m_killed (with_children m) = m_killed m := rfl

@[simp] theorem m_killed_with_sigmask (v : word) (m : Model) :
    m_killed (with_sigmask v m) = m_killed m := rfl

@[simp] theorem m_killed_with_clock (v : word) (m : Model) :
    m_killed (with_clock v m) = m_killed m := rfl

@[simp] theorem m_killed_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_killed (with_accepted v m) = m_killed m := rfl

@[simp] theorem m_killed_with_abort_terminal (v : Bool) (m : Model) :
    m_killed (with_abort_terminal v m) = m_killed m := rfl

@[simp] theorem m_killed_with_sigabrt_pending (m : Model) :
    m_killed (with_sigabrt_pending m) = m_killed m := rfl

@[simp] theorem m_killed_with_killed (v : word) (m : Model) :
    m_killed (with_killed v m) = some v := rfl

@[simp] theorem m_sigabrt_pending_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_sigabrt_pending (with_fds v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_sigabrt_pending (with_pipes v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_vmmaps (v : VmMaps) (m : Model) :
    m_sigabrt_pending (with_vmmaps v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_vm_backing (lz : List (word × word)) (mt : List word)
    (m : Model) :
    m_sigabrt_pending (with_vm_backing lz mt m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_stdin (v : InputStream) (m : Model) :
    m_sigabrt_pending (with_stdin v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_urandom (v : InputStream) (m : Model) :
    m_sigabrt_pending (with_urandom v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_net (v : NetQueue) (m : Model) :
    m_sigabrt_pending (with_net v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_fs (v : Fs.Fs) (m : Model) :
    m_sigabrt_pending (with_fs v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_halted (v : word) (m : Model) :
    m_sigabrt_pending (with_halted v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_tid (v : word) (m : Model) :
    m_sigabrt_pending (with_tid v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_rlimit_core (v : List byte) (m : Model) :
    m_sigabrt_pending (with_rlimit_core v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_utsname (v : List byte) (m : Model) :
    m_sigabrt_pending (with_utsname v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_nofile (v : word) (m : Model) :
    m_sigabrt_pending (with_nofile v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_creds (v : Creds) (m : Model) :
    m_sigabrt_pending (with_creds v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_setsid_succeeded (m : Model) :
    m_sigabrt_pending (with_setsid_succeeded m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_children (m : Model) :
    m_sigabrt_pending (with_children m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_sigmask (v : word) (m : Model) :
    m_sigabrt_pending (with_sigmask v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_clock (v : word) (m : Model) :
    m_sigabrt_pending (with_clock v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_sigabrt_pending (with_accepted v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_abort_terminal (v : Bool) (m : Model) :
    m_sigabrt_pending (with_abort_terminal v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_sigabrt_pending_with_sigabrt_pending (m : Model) :
    m_sigabrt_pending (with_sigabrt_pending m) = true := rfl

@[simp] theorem m_sigabrt_pending_with_killed (v : word) (m : Model) :
    m_sigabrt_pending (with_killed v m) = m_sigabrt_pending m := rfl

@[simp] theorem m_abort_terminal_with_fds (v : List (word × FdEntry)) (m : Model) :
    m_abort_terminal (with_fds v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_pipes (v : List (word × PipeBuf)) (m : Model) :
    m_abort_terminal (with_pipes v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_vmmaps (v : VmMaps) (m : Model) :
    m_abort_terminal (with_vmmaps v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_vm_backing (lz : List (word × word)) (mt : List word)
    (m : Model) :
    m_abort_terminal (with_vm_backing lz mt m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_stdin (v : InputStream) (m : Model) :
    m_abort_terminal (with_stdin v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_urandom (v : InputStream) (m : Model) :
    m_abort_terminal (with_urandom v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_net (v : NetQueue) (m : Model) :
    m_abort_terminal (with_net v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_fs (v : Fs.Fs) (m : Model) :
    m_abort_terminal (with_fs v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_halted (v : word) (m : Model) :
    m_abort_terminal (with_halted v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_tid (v : word) (m : Model) :
    m_abort_terminal (with_tid v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_rlimit_core (v : List byte) (m : Model) :
    m_abort_terminal (with_rlimit_core v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_utsname (v : List byte) (m : Model) :
    m_abort_terminal (with_utsname v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_nofile (v : word) (m : Model) :
    m_abort_terminal (with_nofile v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_creds (v : Creds) (m : Model) :
    m_abort_terminal (with_creds v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_setsid_succeeded (m : Model) :
    m_abort_terminal (with_setsid_succeeded m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_children (m : Model) :
    m_abort_terminal (with_children m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_sigmask (v : word) (m : Model) :
    m_abort_terminal (with_sigmask v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_clock (v : word) (m : Model) :
    m_abort_terminal (with_clock v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_accepted (v : List (word × FdEntry)) (m : Model) :
    m_abort_terminal (with_accepted v m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_abort_terminal (v : Bool) (m : Model) :
    m_abort_terminal (with_abort_terminal v m) = v := rfl

@[simp] theorem m_abort_terminal_with_sigabrt_pending (m : Model) :
    m_abort_terminal (with_sigabrt_pending m) = m_abort_terminal m := rfl

@[simp] theorem m_abort_terminal_with_killed (v : word) (m : Model) :
    m_abort_terminal (with_killed v m) = m_abort_terminal m := rfl

/-- The cross pairs the two changes that added fields to [ProcState]
    owe each other: the alternate-stack bit against the three abort
    fields' setters, and each of those against its setter.  Same
  `rfl`, same reason -- every setter rebuilds [ProcState] and
    carries what it does not write. -/

@[simp] theorem m_killed_with_sigaltstack_installed (m : Model) :
    m_killed (with_sigaltstack_installed m) = m_killed m := rfl

@[simp] theorem m_sigabrt_pending_with_sigaltstack_installed (m : Model) :
    m_sigabrt_pending (with_sigaltstack_installed m) = m_sigabrt_pending m := rfl

@[simp] theorem m_abort_terminal_with_sigaltstack_installed (m : Model) :
    m_abort_terminal (with_sigaltstack_installed m) = m_abort_terminal m := rfl

@[simp] theorem m_sigaltstack_installed_with_killed (v : word) (m : Model) :
    m_sigaltstack_installed (with_killed v m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_sigabrt_pending (m : Model) :
    m_sigaltstack_installed (with_sigabrt_pending m) = m_sigaltstack_installed m := rfl

@[simp] theorem m_sigaltstack_installed_with_abort_terminal (v : Bool) (m : Model) :
    m_sigaltstack_installed (with_abort_terminal v m) = m_sigaltstack_installed m := rfl

theorem m_sigaltstack_installed_init_model (reserved : List (word × word))
    (brk0 mbase sp : word) (lim : Int) (inp : ProcInput) :
    m_sigaltstack_installed (init_model reserved brk0 mbase sp lim inp) = false := rfl

theorem m_fds_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_fds (init_model reserved brk0 mbase sp lim inp) =
      [ (BitVec.ofInt 64 0, FdEntry.FdChannel (BitVec.ofInt 64 0)),
        (BitVec.ofInt 64 1, FdEntry.FdChannel (BitVec.ofInt 64 1)),
        (BitVec.ofInt 64 2, FdEntry.FdChannel (BitVec.ofInt 64 2)) ] := rfl

theorem m_vmmaps_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_vmmaps (init_model reserved brk0 mbase sp lim inp) =
      VmMaps.mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp := rfl

/-- The grant bound of the model a run starts from, in the form the
    examples reason in: [sp] is the section's quantified stack pointer,
    so [lia] closes every bound from [Hsp_lo]/[Hsp_hi].  In the [model]
    rewrite base, unlike its neighbours, because nothing matches on an
    unreduced [alloc_top]. -/

@[simp] theorem alloc_top_init (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    alloc_top (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) =
      (sp.toNat : Int) - stack_max_size := rfl

set_option maxRecDepth 10000 in
/-- A run starts with nothing mapped, no lazy reservation and no page
    materialized, so no backing is charged yet.  Stated over the whole
    [Model] because [vm_backing_used] reads the sparse ledgers in
    [VmState] as well as [vm_maps]; a site that needs the budget conjunct
    of a grant check at the initial model names this rather than trying to
    reduce [vm_backing_used] through the opaque accessors.

  `rfl` still closes it, but `whnf` has to walk the seven-deep `with_*`
  tower of `init_model` down to `[]` in one chain, past Lean's default
  `maxRecDepth` (1000); the option above is scoped to this declaration
  and changes nothing about the statement. -/
theorem vm_backing_used_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    vm_backing_used (init_model reserved brk0 mbase sp lim inp) = (0 : Int) := by
  rfl

theorem m_stdin_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_stdin (init_model reserved brk0 mbase sp lim inp) = inp.in_stdin := rfl

theorem m_urandom_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_urandom (init_model reserved brk0 mbase sp lim inp) = inp.in_urandom := rfl

theorem m_fs_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_fs (init_model reserved brk0 mbase sp lim inp) = in_fs inp := rfl

theorem m_halted_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_halted (init_model reserved brk0 mbase sp lim inp) = none := rfl

theorem m_tid_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_tid (init_model reserved brk0 mbase sp lim inp) = none := rfl

theorem m_rlimit_core_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_rlimit_core (init_model reserved brk0 mbase sp lim inp) = none := rfl

theorem m_nofile_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_nofile (init_model reserved brk0 mbase sp lim inp) = inp.in_nofile := rfl

theorem m_clock_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_clock (init_model reserved brk0 mbase sp lim inp) = BitVec.ofInt 64 0 := rfl

theorem m_net_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_net (init_model reserved brk0 mbase sp lim inp) = inp.in_net := rfl

theorem m_conn_ix_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_conn_ix (init_model reserved brk0 mbase sp lim inp) = BitVec.ofInt 64 0 := rfl

theorem m_creds_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_creds (init_model reserved brk0 mbase sp lim inp) =
      Creds.mkCreds (inp.in_uid) (inp.in_uid) (inp.in_uid)
        (inp.in_gid) (inp.in_gid) (inp.in_gid) (inp.in_groups) := rfl

theorem m_sigmask_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_sigmask (init_model reserved brk0 mbase sp lim inp) = inp.in_sigmask := rfl

theorem m_setsid_succeeded_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_setsid_succeeded (init_model reserved brk0 mbase sp lim inp) = false := rfl

@[simp] theorem m_killed_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_killed (init_model reserved brk0 mbase sp lim inp) = none := rfl

@[simp] theorem m_sigabrt_pending_init_model (reserved : List (word × word))
    (brk0 mbase sp : word) (lim : Int) (inp : ProcInput) :
    m_sigabrt_pending (init_model reserved brk0 mbase sp lim inp) = false := rfl

/-- The declaration arrives from the input and is the only one of the
    three that a run can start with either value of. -/

@[simp] theorem m_abort_terminal_init_model (reserved : List (word × word))
    (brk0 mbase sp : word) (lim : Int) (inp : ProcInput) :
    m_abort_terminal (init_model reserved brk0 mbase sp lim inp) = inp.in_abort_terminal := rfl

theorem m_pipes_init_model (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) :
    m_pipes (init_model reserved brk0 mbase sp lim inp) = [] := rfl


/- =========================================================================
   Sanity checks: the `@[simp]` set actually normalises

  Every lemma in the range IS a computation, so there is nothing left to
  compute here.  The examples below are the two things a
   downstream user does with the set: read a field the setter wrote, and
   read a field it carried.  They are `by simp` rather than `rfl` on
   purpose: `rfl` would prove them with or without the attributes, so it
   would not test the registration.
   ========================================================================= -/

/-- The diagonal: reading what the setter wrote. -/
example (v : List (word × FdEntry)) (m : Model) : m_fds (with_fds v m) = v := by
  simp

/-- ... and the off-diagonal: a setter of another subsystem carries it. -/
example (v : List (word × FdEntry)) (m : Model) :
    m_vmmaps (with_fds v m) = m_vmmaps m := by
  simp

/-- `with_killed` writes the signal into BOTH `m_halted` and `m_killed`, and `with_halted` clears the kill flag, so
  `m_killed (with_halted …)` is `none`. -/
example (sig : word) (m : Model) :
    m_halted (with_killed sig m) = some sig ∧ m_killed (with_killed sig m) = some sig := by
  simp

example (code : word) (m : Model) : m_killed (with_halted code m) = none := by
  simp

/-- The one cross-subsystem right-hand side. -/
example (fs : Fs.Fs) (m : Model) :
    m_statpins (with_fs fs m) = statpins_restrict fs (m_statpins m) := by
  simp

/--... and the `with_statpin` cons. -/
example (p : Fs.path) (bs : List byte) (m : Model) :
    m_statpins (with_statpin p bs m) = (p, bs) :: m_statpins m := by
  simp

/-- The `_mkModel` row. -/
example (fds : List (word × FdEntry)) (vm : VmMaps) (stdin : InputStream)
    (fs : Fs.Fs) (halted : Option word) (tid : Option word)
    (rlim : Option (List byte)) :
    m_fds (mkModel fds vm stdin fs halted tid rlim) = fds ∧
      m_creds (mkModel fds vm stdin fs halted tid rlim) =
        Creds.mkCreds overflow_id overflow_id overflow_id overflow_id
          overflow_id overflow_id [] := by
  simp

/-- A tagged `_init_model` lemma, by the set alone. -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) : m_abort_terminal (init_model reserved brk0 mbase sp lim inp)
      = inp.in_abort_terminal := by
  simp

/-- An UNTAGGED one is proved by naming it — "a site that wants one names
  it": `simp` alone must not see it. -/
example (reserved : List (word × word)) (brk0 mbase sp : word) (lim : Int)
    (inp : ProcInput) : m_nofile (init_model reserved brk0 mbase sp lim inp) = inp.in_nofile := by
  simp only [m_nofile_init_model]
