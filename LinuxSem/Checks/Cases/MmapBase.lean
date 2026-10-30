/-
  * LinuxProcessSem.Checks.Cases.MmapBase — the mmap-base band is the set
    of bases Linux gives

  Mirrors [State.mmap_base_min], [State.mmap_base_max] and
  [Run.valid_mmap_base].  Those notes derive the band from mm/util.c's
  `mmap_base` (Linux v6.18.46, commit 1f99e9ab748f).  This file states
  that computation and proves the band EQUAL to the set of bases it gives
  under a named configuration:

  - the top-down layout (no ADDR_COMPAT_LAYOUT personality,
    `vm.legacy_va_layout` = 0, and the 8 MiB stack limit);
  - `vm.mmap_rnd_bits` at most 24, or a `stack_guard_gap` of at most
    `floor_guard_max` = 0x4aba6a2ab000 bytes (about 74.7 TiB).

  (The model's own note calls that configuration "the configuration
  SCOPE.md names"; the two bullets above ARE that configuration, so they
  are spelled out here rather than referred to.)

  So a launch inside that configuration has its base in the band, and
  every base in the band is one such a launch can have.  The file also
  shows that each named assumption is needed: without it, Linux gives a
  base under the floor.

  Why the floor is not simply lowered to the smallest base Linux can
  give at all: the ASan plan checker reads it.  `Common.AsanInit` starts
  its placement split at `AsanPlanCore.MBASE_MIN`, which is
  `State.mmap_base_min`, and
  `AsanPlacement.kHighMemBeg_below_mmap_base_min` needs the floor above
  the ASan high shadow.  A lower floor would make those proofs false, not
  only longer.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Reason 3 of that file applies: the base is a model constant
  that no trace reveals.

  Spelling differs from the Rocq original in one place, and only there:
  the bit count `bits` is a `Nat`, because Lean's integer power takes a
  `Nat` exponent, and `k < 2 ^ bits` then compares in `Int` through the
  `Nat` cast.  Every other name, hypothesis and number is upstream's.

  The helper lemmas are `private`, as upstream's are `Local`: several of
  them restate page-rounding facts that other modules keep for their own
  use, and hoisting them here would make this example file the home of
  arithmetic the trusted layer does not import.

  Two spellings differ from the Rocq original for Lean reasons, and only
  two: `rand_pad` is `if randomize then stack_rnd_pad else 0` written as a
  `match` (see its own note), and `unclamped_gap_in_domain` is split into
  its `true` and `false` instances, because a literal `Bool` is what makes
  the kernel's `%` an identity argument by argument.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000
-- The four closed-computation examples below share one unfold list, and
-- which of its entries apply depends on the goal they are closing.
set_option linter.unusedSimpArgs false

open LinuxSem.Riscv

namespace LinuxSem.Checks.Cases.MmapBase

/-! ## The kernel's computation, in `Int`

    The kernel computes the gap in `unsigned long`, and so does
    `unclamped_gap`: `pad` wraps at mm/util.c:450, and the test at :452-454
    keeps the gap at the rlimit when `gap + pad` wraps.  The final
    subtraction is kept in `Int`: a NEGATIVE result is a base that wrapped
    below zero in the kernel; the Sv39 section says why no program starts
    from one. -/

/-- `MIN_GAP`, mm/util.c:431. -/
def min_gap : Int := 128 * 1024 * 1024

/-- `MAX_GAP = STACK_TOP / 6 * 5`, mm/util.c:432. -/
def max_gap (stack_top : Int) : Int := stack_top / 6 * 5

/-- `STACK_RND_MASK << PAGE_SHIFT` for a 64-bit task:
    arch/riscv/include/asm/elf.h:56-58 gives the mask 0x3ffff. -/
def stack_rnd_pad : Int := 0x3ffff * LinuxSem.LinuxProcessSem.page_size

/-- `rlim_stack->rlim_cur`: the model's `RLIMIT_STACK` is 8 MiB. -/
def stack_rlimit : Int := 8 * 1024 * 1024

/-- `if randomize then stack_rnd_pad else 0`, the stack pad under
    `PF_RANDOMIZE`.  Written as a `match` rather than an `if` because a
    literal `randomize` then REDUCES: Lean elaborates `if b then x else y`
    for `b : Bool` to `ite (b = true) …`, whose `Decidable` instance is the
    boolean comparison `decEq true true`, so `if true then x else y` is
    propositionally but not definitionally `x`. -/
def rand_pad : Bool → Int
  | true => stack_rnd_pad
  | false => 0

/-- The clamp of mm/util.c:456-459 (`MIN_GAP < MAX_GAP` holds for every
    stack top below). -/
def clamp_gap (stack_top gap : Int) : Int :=
  if gap < min_gap then min_gap
  else if max_gap stack_top < gap then max_gap stack_top
  else gap

/-- `pad` of mm/util.c:446-450 in `unsigned long`: `stack_guard_gap`
    (mm/mmap.c:941-954: 256 pages by default, any page count on the
    command line) plus the stack pad under `PF_RANDOMIZE`. -/
def guard_pad (guard : Int) (randomize : Bool) : Int :=
  (guard + rand_pad randomize) % LinuxSem.LinuxProcessSem.two_pow_64

/-- `gap` before the clamp, mm/util.c:445 and :452-454. -/
def unclamped_gap (guard : Int) (randomize : Bool) : Int :=
  if stack_rlimit + guard_pad guard randomize
      < LinuxSem.LinuxProcessSem.two_pow_64
  then stack_rlimit + guard_pad guard randomize
  else stack_rlimit

/-- `mmap_base(rnd, rlim_stack)`, mm/util.c:434-463.  `randomize` is
    `PF_RANDOMIZE`, which adds the stack pad to the gap and makes
    `arch_pick_mmap_layout` draw `rnd` (mm/util.c:467-470). -/
def topdown_base (stack_top guard : Int) (randomize : Bool) (rnd : Int) : Int :=
  LinuxSem.LinuxProcessSem.page_round_up_Z
    (stack_top - clamp_gap stack_top (unclamped_gap guard randomize) - rnd)

/-- The inputs one launch can have: any page-multiple guard an
    `unsigned long` holds (`val << PAGE_SHIFT`, mm/mmap.c:948-950), and
    `rnd` = `k` pages with `k < 2^bits` (`arch_mmap_rnd`, mm/util.c:399-411),
    `k = 0` without `PF_RANDOMIZE`. -/
def launch_ok (bits : Nat) (guard : Int) (randomize : Bool) (k : Int) : Prop :=
  0 ≤ guard ∧ guard < LinuxSem.LinuxProcessSem.two_pow_64
  ∧ guard % LinuxSem.LinuxProcessSem.page_size = 0
  ∧ 0 ≤ k ∧ k < 2 ^ bits ∧ (randomize = false → k = 0)

/-- The configuration this file names, over the two knobs that move the
    floor.  `vm.mmap_rnd_bits` lies in `mmap_rnd_bits_min ..
    mmap_rnd_bits_max` (the sysctl's range, mm/mmap.c:1528-1536): 18
    (arch/riscv/Kconfig:260-262) to `MMAP_VA_BITS - PAGE_SHIFT - 3`
    (arch/riscv/mm/init.c:850-853, set at boot, :1164-1167), which is 33
    under Sv48 and Sv57 (`MMAP_VA_BITS` is capped at 48,
    arch/riscv/include/asm/pgtable.h:137-140) and 24 under Sv39.  Its boot
    value `CONFIG_ARCH_MMAP_RND_BITS` lies in 18 .. 24
    (arch/Kconfig:1208-1212, arch/riscv/Kconfig:269-271); only root raises
    it past 24, through /proc/sys/vm/mmap_rnd_bits.

    `floor_guard_max` is the largest guard with which even 33 bits keep
    every base at or above the floor: `STACK_TOP - floor - rlimit - stack
    pad - (2^33 - 1) pages`.  It does not depend on the bit count; with
    fewer bits a larger guard would do (about 106.6 TiB at 25). -/
def floor_guard_max : Int := 0x4aba6a2ab000

def named_config (bits : Nat) (guard : Int) : Prop :=
  18 ≤ bits ∧ bits ≤ 33 ∧ (bits ≤ 24 ∨ guard ≤ floor_guard_max)

/-! ## Page rounding and the clamp -/

/-- A page multiple is its own round-up. -/
private theorem page_round_up_Z_id (x : Int)
    (H : x % LinuxSem.LinuxProcessSem.page_size = 0) :
    LinuxSem.LinuxProcessSem.page_round_up_Z x = x := by
  unfold LinuxSem.LinuxProcessSem.page_round_up_Z
    LinuxSem.LinuxProcessSem.page_size at *
  have hdm := Int.mul_ediv_add_emod x 4096
  omega

/-- The round-up is page aligned. -/
private theorem page_round_up_Z_aligned (x : Int) :
    LinuxSem.LinuxProcessSem.page_round_up_Z x
      % LinuxSem.LinuxProcessSem.page_size = 0 := by
  unfold LinuxSem.LinuxProcessSem.page_round_up_Z
    LinuxSem.LinuxProcessSem.page_size
  rw [Int.mul_comm]
  exact Int.mul_emod_right 4096 ((x + 4096 - 1) / 4096)

/-- Rounding up never passes a page boundary at or above `x`. -/
private theorem page_round_up_Z_le (x a : Int)
    (Ha : a % LinuxSem.LinuxProcessSem.page_size = 0) (Hx : x ≤ a) :
    LinuxSem.LinuxProcessSem.page_round_up_Z x ≤ a := by
  unfold LinuxSem.LinuxProcessSem.page_round_up_Z
    LinuxSem.LinuxProcessSem.page_size at *
  have hdm := Int.mul_ediv_add_emod a 4096
  have h0 := Int.emod_nonneg a (b := 4096) (by decide)
  have hlt := Int.emod_lt_of_pos a (b := 4096) (by decide)
  have hbq : a = 4096 * (a / 4096) := by omega
  have h1 : (x + 4096 - 1) / 4096 < a / 4096 + 1 := by
    rw [Int.ediv_lt_iff_lt_mul (by decide : (0 : Int) < 4096)]
    omega
  omega

/-- Rounding up reaches every page boundary less than a page above `x`. -/
private theorem page_round_up_Z_ge (x a : Int)
    (Ha : a % LinuxSem.LinuxProcessSem.page_size = 0) (Hx : a - 4096 < x) :
    a ≤ LinuxSem.LinuxProcessSem.page_round_up_Z x := by
  unfold LinuxSem.LinuxProcessSem.page_round_up_Z
    LinuxSem.LinuxProcessSem.page_size at *
  have hdm := Int.mul_ediv_add_emod a 4096
  have h0 := Int.emod_nonneg a (b := 4096) (by decide)
  have hlt := Int.emod_lt_of_pos a (b := 4096) (by decide)
  have hbq : a = 4096 * (a / 4096) := by omega
  have h1 : a / 4096 ≤ (x + 4096 - 1) / 4096 := by
    rw [Int.le_ediv_iff_mul_le (by decide : (0 : Int) < 4096)]
    omega
  omega

private theorem clamp_gap_id (st g : Int) (H1 : min_gap ≤ g) (H2 : g ≤ max_gap st) :
    clamp_gap st g = g := by
  unfold clamp_gap
  split
  · omega
  · split
    · omega
    · rfl

private theorem clamp_gap_range (st g : Int) (H : min_gap ≤ max_gap st) :
    min_gap ≤ clamp_gap st g ∧ clamp_gap st g ≤ max_gap st
    ∧ clamp_gap st g ≤ max min_gap g := by
  unfold clamp_gap
  split
  · omega
  · split
    · omega
    · omega

private theorem rand_pad_true : rand_pad true = stack_rnd_pad := rfl
private theorem rand_pad_false : rand_pad false = 0 := rfl

private theorem stack_pad_range (randomize : Bool) :
    0 ≤ rand_pad randomize ∧ rand_pad randomize ≤ stack_rnd_pad := by
  cases randomize with
  | true => rw [rand_pad_true]; unfold stack_rnd_pad LinuxSem.LinuxProcessSem.page_size; omega
  | false => rw [rand_pad_false]; simp only [stack_rnd_pad, LinuxSem.LinuxProcessSem.page_size]; omega

/-- Without a wrap the gap is the plain sum.  (Upstream states one lemma
    over `randomize`; the two instances are split here because a literal
    `Bool` is what makes the `%` in `guard_pad` an identity.) -/
private theorem unclamped_gap_true (guard : Int)
    (H0 : 0 ≤ guard)
    (H1 : stack_rlimit + guard + stack_rnd_pad
            < LinuxSem.LinuxProcessSem.two_pow_64) :
    unclamped_gap guard true = stack_rlimit + guard + stack_rnd_pad := by
  obtain ⟨Hp0, Hp1⟩ := stack_pad_range true
  rw [rand_pad_true] at Hp0 Hp1
  simp only [stack_rlimit, stack_rnd_pad, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.page_size] at Hp0 Hp1 H1 ⊢
  have hmod : (guard + 262143 * 4096) % (2 ^ 64) = guard + 262143 * 4096 := by
    apply Int.emod_eq_of_lt <;> omega
  unfold unclamped_gap guard_pad
  rw [rand_pad_true]
  simp only [stack_rlimit, stack_rnd_pad, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.page_size]
  simp only [hmod]
  split <;> omega

private theorem unclamped_gap_false (guard : Int)
    (H0 : 0 ≤ guard)
    (H1 : stack_rlimit + guard + 0 < LinuxSem.LinuxProcessSem.two_pow_64) :
    unclamped_gap guard false = stack_rlimit + guard + 0 := by
  obtain ⟨Hp0, Hp1⟩ := stack_pad_range false
  rw [rand_pad_false] at Hp0 Hp1
  simp only [stack_rlimit, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.page_size] at Hp0 Hp1 H1 ⊢
  have hmod : (guard + 0) % (2 ^ 64) = guard + 0 := by
    apply Int.emod_eq_of_lt <;> omega
  unfold unclamped_gap guard_pad
  rw [rand_pad_false]
  simp only [stack_rlimit, LinuxSem.LinuxProcessSem.two_pow_64]
  simp only [hmod]
  split <;> omega

/-- The `randomize`-general form of the two lemmas above, for callers that
    do not know the flag. -/
private theorem unclamped_gap_in_domain (guard : Int) (randomize : Bool)
    (H0 : 0 ≤ guard)
    (H1 : stack_rlimit + guard + rand_pad randomize
            < LinuxSem.LinuxProcessSem.two_pow_64) :
    unclamped_gap guard randomize = stack_rlimit + guard + rand_pad randomize := by
  cases randomize with
  | true =>
    rw [rand_pad_true] at H1 ⊢
    exact unclamped_gap_true guard H0 H1
  | false =>
    rw [rand_pad_false] at H1 ⊢
    exact unclamped_gap_false guard H0 H1

private theorem topdown_base_randomized (st guard rnd : Int)
    (H0 : 0 ≤ guard)
    (H1 : stack_rlimit + guard + stack_rnd_pad
            < LinuxSem.LinuxProcessSem.two_pow_64) :
    topdown_base st guard true rnd
      = LinuxSem.LinuxProcessSem.page_round_up_Z
          (st - clamp_gap st (stack_rlimit + guard + stack_rnd_pad) - rnd) := by
  unfold topdown_base
  rw [unclamped_gap_true guard H0 H1]

private theorem topdown_base_fixed (st guard rnd : Int)
    (H0 : 0 ≤ guard)
    (H1 : stack_rlimit + guard + 0 < LinuxSem.LinuxProcessSem.two_pow_64) :
    topdown_base st guard false rnd
      = LinuxSem.LinuxProcessSem.page_round_up_Z
          (st - clamp_gap st (stack_rlimit + guard + 0) - rnd) := by
  unfold topdown_base
  rw [unclamped_gap_false guard H0 H1]

private theorem two_pow_64_val :
    LinuxSem.LinuxProcessSem.two_pow_64 = 18446744073709551616 := by
  decide

private theorem sv48_domain :
    LinuxSem.LinuxProcessSem.sp_window_hi + stack_rnd_pad
      < LinuxSem.LinuxProcessSem.two_pow_64 := by
  unfold LinuxSem.LinuxProcessSem.sp_window_hi stack_rnd_pad
    LinuxSem.LinuxProcessSem.two_pow_64 LinuxSem.LinuxProcessSem.page_size
  decide

private theorem sv39_domain :
    LinuxSem.LinuxProcessSem.sv39_task_size + stack_rnd_pad
      < LinuxSem.LinuxProcessSem.two_pow_64 := by
  unfold LinuxSem.LinuxProcessSem.sv39_task_size stack_rnd_pad
    LinuxSem.LinuxProcessSem.two_pow_64 LinuxSem.LinuxProcessSem.page_size
  decide

private theorem max_gap_sv48 :
    max_gap LinuxSem.LinuxProcessSem.sp_window_hi = 0x6aaaaaaaaaa9 := by
  unfold max_gap LinuxSem.LinuxProcessSem.sp_window_hi
  decide

private theorem max_gap_sv39 :
    max_gap LinuxSem.LinuxProcessSem.sv39_task_size = 0x3555555552 := by
  unfold max_gap LinuxSem.LinuxProcessSem.sv39_task_size
  decide

/-- The value of a page-aligned `x` as a whole number of pages. -/
private theorem eq_mul_ediv_of_aligned (x : Int)
    (H : x % LinuxSem.LinuxProcessSem.page_size = 0) :
    x = LinuxSem.LinuxProcessSem.page_size * (x / LinuxSem.LinuxProcessSem.page_size) := by
  unfold LinuxSem.LinuxProcessSem.page_size at *
  have hdm := Int.mul_ediv_add_emod x 4096
  omega

/-! Every page-aligned `b` from the base of the largest page-multiple gap
    `gmax` with the largest draw of `kmax` pages, up to
    `STACK_TOP - MIN_GAP`, is a base some launch has: inside the top-down
    range of `gmax` the guard sets the gap exactly and nothing is drawn;
    below it the gap is `gmax` and the draw makes up the rest.

    `Hg4` (`gmax <= st`) is consumed only by `omega`, inside branch 1's
    `gmax < two_pow_64` bound, so it is named here rather than left to be
    inferred. -/
set_option linter.unusedVariables false in
private theorem every_aligned_base_is_reached (st gmax kmax b : Int)
    (Hkmax : 0 ≤ kmax)
    (Hst : st % LinuxSem.LinuxProcessSem.page_size = 0)
    (Hg : gmax % LinuxSem.LinuxProcessSem.page_size = 0)
    (Hg1 : stack_rlimit + stack_rnd_pad ≤ gmax) (Hg2 : gmax ≤ max_gap st)
    (Hg3 : min_gap ≤ gmax) (Hg4 : gmax ≤ st)
    (Hdom : st + stack_rnd_pad < LinuxSem.LinuxProcessSem.two_pow_64)
    (Hb : b % LinuxSem.LinuxProcessSem.page_size = 0) (Hb0 : 0 ≤ b)
    (Hlo : st - gmax - kmax * LinuxSem.LinuxProcessSem.page_size ≤ b)
    (Hhi : b ≤ st - min_gap) :
    ∃ (guard : Int) (randomize : Bool) (k : Int),
      0 ≤ guard ∧ guard % LinuxSem.LinuxProcessSem.page_size = 0
      ∧ stack_rlimit + guard + stack_rnd_pad
          < LinuxSem.LinuxProcessSem.two_pow_64
      ∧ 0 ≤ k ∧ k ≤ kmax ∧ (randomize = false → k = 0)
      ∧ b = topdown_base st guard randomize (k * LinuxSem.LinuxProcessSem.page_size) := by
  obtain ⟨s, hs⟩ : ∃ s, st = 4096 * s :=
    ⟨st / 4096, eq_mul_ediv_of_aligned st Hst⟩
  obtain ⟨g, hg⟩ : ∃ g, gmax = 4096 * g :=
    ⟨gmax / 4096, eq_mul_ediv_of_aligned gmax Hg⟩
  obtain ⟨m, hm⟩ : ∃ m, b = 4096 * m :=
    ⟨b / 4096, eq_mul_ediv_of_aligned b Hb⟩
  have hR : stack_rlimit = 8388608 := by decide
  have hP : stack_rnd_pad = 1073737728 := by decide
  have hM : min_gap = 134217728 := by decide
  have hT : LinuxSem.LinuxProcessSem.two_pow_64 = 18446744073709551616 := by decide
  simp only [LinuxSem.LinuxProcessSem.page_size] at *
  by_cases Hb' : b < st - gmax
  · -- inside the top-down range: the guard sets the gap, nothing is drawn
    refine ⟨gmax - stack_rlimit - stack_rnd_pad, true, s - g - m,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · have hg' : gmax - stack_rlimit - stack_rnd_pad
          = 4096 * (g - 2048 - 262143) := by omega
      rw [hg']
      exact Int.mul_emod_right 4096 _
    · omega
    · omega
    · omega
    · intro h; exact absurd h (by decide)
    · rw [topdown_base_randomized _ _ _ (by omega) (by omega)]
      rw [show stack_rlimit + (gmax - stack_rlimit - stack_rnd_pad) + stack_rnd_pad
            = gmax from by omega]
      rw [clamp_gap_id st gmax (by omega) (by omega)]
      rw [show st - gmax - (s - g - m) * 4096 = b from by omega]
      exact (page_round_up_Z_id b Hb).symm
  · -- out of it: the gap is `gmax` and the draw makes up the rest
    refine ⟨st - b - stack_rlimit, false, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · have hs' : st - b - stack_rlimit = 4096 * (s - m - 2048) := by omega
      rw [hs']
      exact Int.mul_emod_right 4096 _
    · omega
    · omega
    · omega
    · intro _; rfl
    · rw [topdown_base_fixed _ _ _ (by omega) (by omega)]
      rw [show stack_rlimit + (st - b - stack_rlimit) + 0 = st - b from by omega]
      rw [clamp_gap_id st (st - b) (by omega) (by omega)]
      rw [show st - (st - b) - 0 * 4096 = b from by omega]
      exact (page_round_up_Z_id b Hb).symm

/-! ## Sv48 (and Sv57, which has the same stack top and the same bit range)

    The band is EXACTLY the set of bases the named configuration gives.
    Left to right needs only `bits = 24`: the floor is the base with the
    largest gap and the largest 24-bit draw.  Right to left is the
    derivation in `State.mmap_base_min`'s note, for every input. -/

/-- The bit-count comparison `2^m ≤ 2^n` in `Int`, through `Nat`. -/
private theorem pow_two_le {m n : Nat} (H : m ≤ n) : (2 : Int) ^ m ≤ (2 : Int) ^ n := by
  have h1 : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) H
  have h2 : ((2 ^ m : Nat) : Int) ≤ ((2 ^ n : Nat) : Int) := Int.ofNat_le.mpr h1
  simpa using h2

def sv48_linux_base (b : Int) : Prop :=
  ∃ (bits : Nat) (guard : Int) (randomize : Bool) (k : Int),
    named_config bits guard ∧ launch_ok bits guard randomize k
    ∧ b = topdown_base LinuxSem.LinuxProcessSem.sp_window_hi guard randomize
            (k * LinuxSem.LinuxProcessSem.page_size)

theorem sv48_band_is_linux_set (w : word) :
    LinuxSem.LinuxProcessSem.Run.valid_mmap_base w
      ↔ sv48_linux_base ((w.toNat : Int)) := by
  unfold LinuxSem.LinuxProcessSem.Run.valid_mmap_base sv48_linux_base
    named_config launch_ok
  have hS : LinuxSem.LinuxProcessSem.page_size = 4096 := by decide
  have hR : stack_rlimit = 8388608 := by decide
  have hP : stack_rnd_pad = 1073737728 := by decide
  have hM : min_gap = 134217728 := by decide
  have hW : LinuxSem.LinuxProcessSem.sp_window_hi = 140737488355328 := by decide
  have hT : LinuxSem.LinuxProcessSem.two_pow_64 = 18446744073709551616 := by decide
  constructor
  · rintro ⟨Hlo, Hhi, Hal⟩
    simp only [LinuxSem.LinuxProcessSem.mmap_base_min,
      LinuxSem.LinuxProcessSem.mmap_base_max,
      LinuxSem.LinuxProcessSem.sp_window_hi] at Hlo Hhi
    obtain ⟨guard, randomize, k, H1, H2, H3, H4, H5, H6, H7⟩ :=
      every_aligned_base_is_reached LinuxSem.LinuxProcessSem.sp_window_hi
        0x6aaaaaaaa000 16777215 ((w.toNat : Int))
        (by decide) (by decide) (by decide) (by decide)
        (by rw [max_gap_sv48]; decide)
        (by decide) (by decide) sv48_domain Hal (by omega)
        (by omega) (by omega)
    exact ⟨24, guard, randomize, k, ⟨by omega, by omega, Or.inl (by omega)⟩,
           ⟨H1, by omega, H2, H4, by omega, H6⟩, H7⟩
  · rintro ⟨bits, guard, randomize, k, ⟨Hb1, Hb2, Hcfg⟩,
             ⟨Hg0, Hglt, Hgal, Hk, Hk0, _⟩, Heq⟩
    rw [Heq]
    unfold topdown_base
    obtain ⟨Hc1, Hc2, Hc3⟩ :=
      clamp_gap_range LinuxSem.LinuxProcessSem.sp_window_hi
        (unclamped_gap guard randomize) (by rw [max_gap_sv48]; unfold min_gap; omega)
    rw [max_gap_sv48] at Hc2
    refine ⟨?_, ?_, page_round_up_Z_aligned _⟩
    · -- the floor
      apply page_round_up_Z_ge _ _ (by decide)
      unfold LinuxSem.LinuxProcessSem.mmap_base_min
        LinuxSem.LinuxProcessSem.sp_window_hi
        LinuxSem.LinuxProcessSem.page_size at *
      rcases Hcfg with Hbits | Hguard
      · have hpow : (2 : Int) ^ bits ≤ 16777216 := by
          have h := pow_two_le Hbits
          rwa [show ((2 : Int) ^ (24 : Nat)) = 16777216 from by decide] at h
        omega
      · have hpow : (2 : Int) ^ bits ≤ 8589934592 := by
          have h := pow_two_le Hb2
          rwa [show ((2 : Int) ^ (33 : Nat)) = 8589934592 from by decide] at h
        have hpad := (stack_pad_range randomize).2
        have hdom : stack_rlimit + guard + rand_pad randomize
            < LinuxSem.LinuxProcessSem.two_pow_64 := by
          unfold stack_rlimit stack_rnd_pad floor_guard_max
            LinuxSem.LinuxProcessSem.two_pow_64
            LinuxSem.LinuxProcessSem.page_size at *
          omega
        rw [unclamped_gap_in_domain guard randomize Hg0 hdom] at *
        unfold floor_guard_max stack_rlimit stack_rnd_pad min_gap
          LinuxSem.LinuxProcessSem.page_size at *
        omega
    · -- the cap
      apply page_round_up_Z_le _ _ (by decide)
      unfold LinuxSem.LinuxProcessSem.mmap_base_max min_gap
        LinuxSem.LinuxProcessSem.sp_window_hi
        LinuxSem.LinuxProcessSem.page_size at *
      omega

/-! ## Each assumption is needed

    With 25 bits and a guard that drives the gap to its largest page
    multiple, the draw of 2^24 pages gives 0x154555556000, one page under
    the floor. -/
theorem rnd_bits_25_and_a_huge_guard_go_below_the_floor :
    launch_ok 25 (0x6aaaaaaaa000 - stack_rlimit - stack_rnd_pad) true (2 ^ 24)
  ∧ topdown_base LinuxSem.LinuxProcessSem.sp_window_hi
      (0x6aaaaaaaa000 - stack_rlimit - stack_rnd_pad) true
      (2 ^ 24 * LinuxSem.LinuxProcessSem.page_size) = 0x154555556000
  ∧ 0x154555556000 < LinuxSem.LinuxProcessSem.mmap_base_min := by
  simp only [launch_ok, named_config, floor_guard_max, stack_rlimit, stack_rnd_pad,
    rand_pad, LinuxSem.LinuxProcessSem.page_size, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.sp_window_hi, LinuxSem.LinuxProcessSem.mmap_base_min,
    topdown_base, guard_pad, unclamped_gap, clamp_gap, max_gap, min_gap,
    LinuxSem.LinuxProcessSem.page_round_up_Z]
  decide

/-- The legacy layout puts the base at `TASK_UNMAPPED_BASE` plus the draw
    (mm/util.c:472-474), where `TASK_UNMAPPED_BASE` is
    `PAGE_ALIGN(2^MMAP_MIN_VA_BITS / 3)` with `MMAP_MIN_VA_BITS` = 39 for
    a 64-bit task (arch/riscv/include/asm/processor.h:52,
    arch/riscv/include/asm/pgtable.h:138-140).  Without a draw that is far
    under the floor. -/
def task_unmapped_base : Int :=
  LinuxSem.LinuxProcessSem.page_round_up_Z (2 ^ 39 / 3)

theorem legacy_base_is_below_the_floor :
    task_unmapped_base = 0x2aaaaab000
  ∧ task_unmapped_base < LinuxSem.LinuxProcessSem.mmap_base_min := by
  simp only [launch_ok, named_config, floor_guard_max, stack_rlimit, stack_rnd_pad,
    rand_pad, LinuxSem.LinuxProcessSem.page_size, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.sp_window_hi, LinuxSem.LinuxProcessSem.mmap_base_min,
    topdown_base, guard_pad, unclamped_gap, clamp_gap, max_gap, min_gap,
    LinuxSem.LinuxProcessSem.page_round_up_Z]
  decide

/-- And the clause that covers the hardened setting: root raises
    `vm.mmap_rnd_bits` to 33 and leaves the guard at its default 256 pages.
    The lowest base that gives is 0x5fffbf702000, well inside the band, so
    that setting is in the model. -/
theorem rnd_bits_33_default_guard_is_in_the_band :
    named_config 33 (256 * LinuxSem.LinuxProcessSem.page_size)
  ∧ topdown_base LinuxSem.LinuxProcessSem.sp_window_hi
      (256 * LinuxSem.LinuxProcessSem.page_size) true
      ((2 ^ 33 - 1) * LinuxSem.LinuxProcessSem.page_size) = 0x5fffbf702000
  ∧ LinuxSem.LinuxProcessSem.mmap_base_min ≤ 0x5fffbf702000 := by
  simp only [launch_ok, named_config, floor_guard_max, stack_rlimit, stack_rnd_pad,
    rand_pad, LinuxSem.LinuxProcessSem.page_size, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.sp_window_hi, LinuxSem.LinuxProcessSem.mmap_base_min,
    topdown_base, guard_pad, unclamped_gap, clamp_gap, max_gap, min_gap,
    LinuxSem.LinuxProcessSem.page_round_up_Z]
  decide

/-- `floor_guard_max` is exact: at 33 bits with the largest draw, that
    guard gives the floor itself and one page more gives a base one page
    under it. -/
theorem floor_guard_max_is_tight :
    topdown_base LinuxSem.LinuxProcessSem.sp_window_hi floor_guard_max true
      ((2 ^ 33 - 1) * LinuxSem.LinuxProcessSem.page_size)
      = LinuxSem.LinuxProcessSem.mmap_base_min
  ∧ launch_ok 33 (floor_guard_max + LinuxSem.LinuxProcessSem.page_size) true
      (2 ^ 33 - 1)
  ∧ topdown_base LinuxSem.LinuxProcessSem.sp_window_hi
      (floor_guard_max + LinuxSem.LinuxProcessSem.page_size) true
      ((2 ^ 33 - 1) * LinuxSem.LinuxProcessSem.page_size)
      = LinuxSem.LinuxProcessSem.mmap_base_min - LinuxSem.LinuxProcessSem.page_size := by
  simp only [launch_ok, named_config, floor_guard_max, stack_rlimit, stack_rnd_pad,
    rand_pad, LinuxSem.LinuxProcessSem.page_size, LinuxSem.LinuxProcessSem.two_pow_64,
    LinuxSem.LinuxProcessSem.sp_window_hi, LinuxSem.LinuxProcessSem.mmap_base_min,
    topdown_base, guard_pad, unclamped_gap, clamp_gap, max_gap, min_gap,
    LinuxSem.LinuxProcessSem.page_round_up_Z]
  decide

/-! ## Sv39

    `STACK_TOP` is 2^38 and `mmap_rnd_bits_max` is 24, so the subtraction
    can go below zero and wrap.  Such a base gives no program: the vDSO's
    `get_unmapped_area` (arch/riscv/kernel/vdso.c:124-127) takes the
    top-down search with `high_limit` = the wrapped base (mm/mmap.c:766),
    which finds the free range above the stack (mm/vma.c:2942-2982) and
    answers an address above `TASK_SIZE`; `__get_unmapped_area` turns that
    into -ENOMEM (mm/mmap.c:857-858), `load_elf_binary` fails past the
    point of no return (fs/binfmt_elf.c:1290-1293) and `bprm_execve` kills
    the task (fs/exec.c:1774-1775).  So the Sv39 band is every page-aligned
    base from 0 to the cap, and it is exactly the set of non-wrapped bases.
    Base 0 is in that set and also starts no program: the search's top is
    then `0 - 1` = `ULONG_MAX` (mm/vma.h:502), so the vDSO search fails as
    for a wrapped base.  The band keeps it, a precision cost only, since no
    spec arm reads the base. -/

def sv39_linux_base (b : Int) : Prop :=
  ∃ (guard : Int) (randomize : Bool) (k : Int),
    launch_ok 24 guard randomize k
    ∧ b = topdown_base LinuxSem.LinuxProcessSem.sv39_task_size guard randomize
            (k * LinuxSem.LinuxProcessSem.page_size)

theorem sv39_band_is_linux_set (w : word) :
    LinuxSem.LinuxProcessSem.Run.valid_mmap_base_va .Sv39 w
      ↔ sv39_linux_base ((w.toNat : Int)) := by
  unfold LinuxSem.LinuxProcessSem.Run.valid_mmap_base_va sv39_linux_base
    launch_ok
  simp only [LinuxSem.LinuxProcessSem.va_mmap_base_min,
    LinuxSem.LinuxProcessSem.va_mmap_base_max,
    LinuxSem.LinuxProcessSem.va_stack_top]
  have hS : LinuxSem.LinuxProcessSem.page_size = 4096 := by decide
  have hR : stack_rlimit = 8388608 := by decide
  have hP : stack_rnd_pad = 1073737728 := by decide
  have hM : min_gap = 134217728 := by decide
  have hT : LinuxSem.LinuxProcessSem.two_pow_64 = 18446744073709551616 := by decide
  have hS39 : LinuxSem.LinuxProcessSem.sv39_task_size = 274877906944 := by decide
  constructor
  · rintro ⟨_, Hhi, Hal⟩
    obtain ⟨guard, randomize, k, H1, H2, H3, H4, H5, H6, H7⟩ :=
      every_aligned_base_is_reached LinuxSem.LinuxProcessSem.sv39_task_size
        0x3555555000 16777215 ((w.toNat : Int))
        (by decide) (by decide) (by decide) (by decide)
        (by rw [max_gap_sv39]; decide)
        (by decide) (by decide) sv39_domain Hal (by omega)
        (by omega) (by omega)
    exact ⟨guard, randomize, k, ⟨H1, by omega, H2, H4, by omega, H6⟩, H7⟩
  · rintro ⟨guard, randomize, k, ⟨Hg0, Hglt, Hgal, Hk, Hk0, _⟩, Heq⟩
    obtain ⟨Hc1, Hc2, _⟩ :=
      clamp_gap_range LinuxSem.LinuxProcessSem.sv39_task_size
        (unclamped_gap guard randomize)
        (by rw [max_gap_sv39]; unfold min_gap; omega)
    rw [max_gap_sv39] at Hc2
    refine ⟨by trace_state; omega, ?_, ?_⟩
    · rw [Heq]
      unfold topdown_base
      apply page_round_up_Z_le _ _ (by decide)
      unfold LinuxSem.LinuxProcessSem.sv39_task_size min_gap
        LinuxSem.LinuxProcessSem.page_size at *
      omega
    · rw [Heq]
      exact page_round_up_Z_aligned _

end LinuxSem.Checks.Cases.MmapBase
