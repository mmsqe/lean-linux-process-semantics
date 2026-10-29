/-
  * LinuxProcessSem.Checks.Cases.Brk — where the initial program break can be

  Worked cases over [State.brk_aslr_max] and the predicate that reads it,
  [Run.valid_brk].  What there is to pin is the EDGE of the band, in
  both directions: the last placement the band admits, and the next
  page up, which it refuses.  A bound only says something where it is
  tight, and a bound nothing sits against can be widened without a
  single proof going red.

  The cap IS the kernel's reach: [arch_randomize_brk] stops exactly
  1 GiB above the page-rounded image top and attains it (the derivation
  is on [State.brk_aslr_max]).  So the two numbers here are that reach,
  admitted, and the page above it, refused.  Widening the band — to a
  round number such as 2 GiB, or to the reach plus one spare page —
  turns the refusal red, which is the point of writing it down.

  These are worked cases, not the trusted specification: they are read
  off the definitions without running a binary.  `Checks.Examples`
  re-exports this module the way it re-exports the rest of
  `Checks.Cases`.

  Spelling.  `Z` is `Int`, `word` is `BitVec 64`, `Z_to_bv 64 z` is
  `BitVec.ofInt 64 z`, `bv_unsigned w` is `(w.toNat : Int)`; the names
  `reserved_top`/`valid_brk`/`brk_aslr_max`/`segments_reserved` are this
  tree's.  Every goal below is a closed decidable proposition, so
  `decide` discharges it; the two comparisons that read a `BitVec` go
  through `toNat` and close the same way.
-/
import LinuxSem.LinuxProcessSem.Run

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType

namespace LinuxSem.Checks.Cases.Brk

/-- An image whose LOAD reservations put the page-rounded top at
    0x14000, the top three of this tree's examples are written against
    ([Examples/brk_rev_ns], [Examples/alloc_join_ns]).  The statements
    below are about any [MemImageType.Segment] list that reserves this,
    rather than about a segment value, for the reason
    `Checks.VmMapsDisjoint`'s witness gives: a [Segment] carries a
    primitive-string payload, and naming one would put that payload into
    these cases' assumptions. -/
def brk_edge_reserved : List (word × word) :=
  [(BitVec.ofInt 64 0x10000, BitVec.ofInt 64 0x4000)]

theorem brk_edge_reserved_top : reserved_top brk_edge_reserved = 0x14000 := by
  decide

/-- The furthest a kernel reaches: one page above the image top, plus the
    largest displacement [randomize_page(_, SZ_1G)] can draw, which is
    1 GiB less one page.  The two cancel, so the reach is exactly 1 GiB
    above the top. -/
def brk_at_kernel_reach : word :=
  BitVec.ofInt 64 (0x14000 + 1024 * 1024 * 1024)

/-- And the page past the reach, which the band refuses. -/
def brk_past_band_cap : word :=
  BitVec.ofInt 64 (0x14000 + 1024 * 1024 * 1024 + 4096)

theorem brk_at_the_kernels_reach_is_admitted (segs : List Segment)
    (Hs : segments_reserved segs = brk_edge_reserved) :
    valid_brk segs brk_at_kernel_reach := by
  unfold valid_brk
  rw [Hs]
  unfold brk_edge_reserved brk_at_kernel_reach brk_aslr_max page_size
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem brk_one_page_past_the_kernels_reach_is_refused (segs : List Segment)
    (Hs : segments_reserved segs = brk_edge_reserved) :
    ¬ valid_brk segs brk_past_band_cap := by
  unfold valid_brk
  rw [Hs]
  unfold brk_edge_reserved brk_past_band_cap brk_aslr_max page_size
  intro H
  exact absurd H.2.1 (by decide)

/-- The refusal above is by the CAP, not by alignment: the page past the
    reach is page-aligned and above the image top, so the two conjuncts
    the statement is not about are both satisfied and cannot be what
    refuses it. -/
theorem brk_past_the_band_cap_meets_the_other_two_conjuncts :
    reserved_top brk_edge_reserved ≤ (brk_past_band_cap.toNat : Int)
    ∧ (brk_past_band_cap.toNat : Int) % page_size = 0 := by
  unfold brk_edge_reserved brk_past_band_cap page_size
  constructor <;> decide

/-- The floor is the image top itself, which is where a kernel with
    randomisation off leaves the break, and the page below it is
    refused. -/
theorem brk_at_the_image_top_is_admitted (segs : List Segment)
    (Hs : segments_reserved segs = brk_edge_reserved) :
    valid_brk segs (BitVec.ofInt 64 0x14000) := by
  unfold valid_brk
  rw [Hs]
  unfold brk_edge_reserved brk_aslr_max page_size
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem brk_one_page_below_the_image_top_is_refused (segs : List Segment)
    (Hs : segments_reserved segs = brk_edge_reserved) :
    ¬ valid_brk segs (BitVec.ofInt 64 0x13000) := by
  unfold valid_brk
  rw [Hs]
  unfold brk_edge_reserved brk_aslr_max page_size
  intro H
  exact absurd H.1 (by decide)

end LinuxSem.Checks.Cases.Brk
