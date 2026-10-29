/-
  * Common.SpecConsts — the ONE place where numeric values of trusted-spec
    constants are exposed to the proofs.

    [Uaccess.rw_bytes_max] = 2^17 = 131072.  No other file may unfold it.

  The constant is reached through the `Sys.Uaccess` namespace, which is where
  this tree defines it, so no module outside this one has to unfold the bound.
-/
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Sys.Uaccess

namespace LinuxSem.Common.SpecConsts

open LinuxSem.LinuxProcessSem.Sys.Uaccess

/-- The trusted transfer bound is at least 2^17. -/
theorem rw_bytes_max_ge17 : (131072 : Int) ≤ rw_bytes_max := by
  unfold rw_bytes_max
  omega

/-- The trusted transfer bound is non-negative. -/
theorem rw_bytes_max_nonneg : (0 : Int) ≤ rw_bytes_max := by
  have := rw_bytes_max_ge17
  omega

end LinuxSem.Common.SpecConsts
