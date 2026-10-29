/-
  * Examples.RwxFlagNs.RwxFlagNsDefs — shared definitions and image facts


  PROOF-SIDE FILE (not part of the trusted specification).

  Both binaries store 5 into a writable global byte, load it back, and
  exit with it: no output, exit code 5, on every input.

  What the example is FOR is the source binary's layout: it is linked
  (`source/rwx.lds`, via `source/ldflags.txt`) into a SINGLE RWX LOAD
  segment holding the ELF headers, `.text`, and the writable data — the
  merged layout GNU ld's default `-z noseparate-code` produces — so every
  instruction fetch goes through the model's overlay-aware w+x fetch
  (`RiscvSemantics.code_read_ov`), and both of its stores (musl's
  `__environ` slot in `.bss`, and `flag`) land in the same segment the code
  executes from.  The proof carries `WxExec.mem_clear` — "the overlay
  misses the `.text` range `[0x10078, 0x100e4)`" — as the frame invariant
  that lets the generated static `fetch_word_wx` facts close each step's
  fetch.  The target is an ordinary lld-linked binary (immutable r-x code),
  so its side of the proof is the standard static-fetch machinery.

  NOTE ON THE BUILD INPUTS.  The sources also ship `source/program.c`,
  `source/rwx.lds`, `source/ldflags.txt` and `target/program.zig` — the two
  programs and the link script — and builds the binaries with musl-gcc and
  zig.  Those build products are what the two `*MemImage` snapshots freeze,
  so the demo's subject (the linked IMAGE) is carried entirely by them.
  No assembly is ported: there is none in this directory, `_start` comes
  from musl's `crt1` and lld's own entry stub, and both are already inside
  the snapshotted segment bytes.

  NOTE ON THE GENERATED ALIASES.  `source_segs`,
  `source_phdrs`, `target_segs` and `target_phdrs` live in
  `rwx_flag_ns_code.v`, a file `dune` GENERATES per build
  (`tools/gen_fd_lemmas.py`) and does not check in.  They are three-line
  aliases of the snapshot modules' definitions, so they are declared here,
  where every file of the directory can
  see them.  The same generated file also emits the per-instruction
  `SF_`/`SD_`/`TF_`/`TD_` fetch and decode facts; the port emits each
  side's facts at the top of that side's proof file
  (`RwxFlagNsSource.lean`, `RwxFlagNsTarget.lean`), with the same
  statements and the same obligation — every one of them still has to
  check against the image.
-/
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.StreamSim
import LinuxSem.Common.StoreOk
import LinuxSem.Common.MmapSim
import LinuxSem.Common.WxExec
import LinuxSem.Examples.RwxFlagNs.SourceMemImage
import LinuxSem.Examples.RwxFlagNs.TargetMemImage

/- `autoImplicit` is off: in a STATEMENT a bare identifier would otherwise
   become an implicitly bound variable, i.e. a weakened claim rather than a
   compile error. -/
set_option autoImplicit false

/- The payload computations below reduce the model's hex decoder over the
   4 KiB segment images — deeper and longer than the default `decide`
   budgets.  Resource knobs, not proof steps: they buy the same kernel
   check more room, they do not let anything through unchecked. -/
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.StreamSim
open LinuxSem.Common.StoreOk
open LinuxSem.Common.MmapSim
open LinuxSem.Common.WxExec

namespace LinuxSem.Examples.RwxFlagNs

/-- The FP state at process entry, so that the `StoreOk`/`PropExec` lemmas
    (whose proofs go through a `machine_state`) elaborate.  Same local
    instance `WxExec.lean`, `SpinAlg.lean` and `DrainAlg.lean` declare. -/
local instance rwx_fx : FPState := LinuxSem.Common.PropExec.fx0

/- ######################################################################### -/
/- Entry points                                                              -/
/- ######################################################################### -/

/-- The source image's LOAD segments, under the name the generated
    `rwx_flag_ns_code.v` gives them (see the port note in the header). -/
def source_segs : List Segment := SourceMemImage.SourceMemImage_loaded_segments

def source_phdrs : PhdrInfo := SourceMemImage.SourceMemImage_phdrs

/-- The target image's LOAD segments. -/
def target_segs : List Segment := TargetMemImage.TargetMemImage_loaded_segments

def target_phdrs : PhdrInfo := TargetMemImage.TargetMemImage_phdrs

theorem source_init_pc_val : SourceMemImage.SourceMemImage_init_pc = 0x10078 := by
  decide

theorem target_init_pc_val : TargetMemImage.TargetMemImage_init_pc = 0x1001190 := by
  decide

/- ######################################################################### -/
/- The source image is ALL w+x: the static fetch declines everywhere         -/
/- ######################################################################### -/

/-- The source's single LOAD segment carries `x` AND `w`, so the static
    fetch's `x /\ ~w` gate rejects every address of the image: the
    overlay-aware w+x path is the only one that can succeed there. -/
theorem source_no_ro_exec : no_ro_exec source_segs = true := by
  decide

/-- The source's `.text` range: the `mem_clear` frame invariant is stated
    over it, and every fetched pc lies inside it. -/
def stext_lo : Int := 0x10078

def stext_hi : Int := 0x100e4

/- ######################################################################### -/
/- Payload density                                                          -/
/- ######################################################################### -/

/-! The window facts `source_wseg` and `target_wseg` need all 4 KiB of
    segment and checks that every byte of the window is present and
    writable.  Two Lean facts make that route unavailable, so the port
    takes a structural one instead:

    - `native_decide` is the only VM-backed proof step Lean offers, and it
      rests on an extra postulate; this development admits none.  Kernel
      reduction of the hex decoder, on the other hand, is quadratic in the
      length of a hex chunk (`hex_byte_at` materialises the chunk's
      character list), so deciding `wseg_ok` byte by byte over 4096 bytes
      does not finish.

    So the two things computation was used for are established directly:
    the payload is DENSE (every offset below the segment size decodes —
    `segment_byte_at_isSome` below, which needs only that every character
    is a hex digit and that the chunk lengths add up), and the segment
    covering the window is WRITABLE.  `wseg_ok_of_dense` then inducts.
    Nothing is assumed: the `by decide` facts at each instantiation still
    check every hex digit of the 4 KiB payload — they just do it once,
    instead of once per address.

    This section is proof
    infrastructure for the same two theorems. -/

/-- Number of bytes a chunk list spells out: the sum of the chunks'
    character counts, halved. -/
def chunk_bytes : List String → Nat
  | [] => 0
  | s :: r => s.length / 2 + chunk_bytes r

/-- Every character of the chunk is a hex digit — the side condition
    `hex_byte_at` needs in order to return a byte rather than `none`. -/
def chunk_hex (s : String) : Bool :=
  s.toList.all (fun c => decide (hex_nybble c < 16))

/-- `hex_byte_at` is defined at every in-range byte index of an all-hex
    chunk.  (`hex_byte_at` clears its two-digit bound at `2i+1 < s.length`
    and afterwards refuses only a non-hex character or a short string.) -/
theorem hex_byte_at_isSome {s : String} {i : Nat}
    (hi : 2 * i + 1 < s.length) (hok : chunk_hex s = true) :
    (hex_byte_at s i).isSome = true := by
  rw [chunk_hex, List.all_eq_true] at hok
  have hlen : 2 * i + 1 < s.toList.length := by
    rw [String.length_toList]; exact hi
  have h0 : s.toList[2 * i]? = some s.toList[2 * i] :=
    List.getElem?_eq_getElem (by omega)
  have h1 : s.toList[2 * i + 1]? = some s.toList[2 * i + 1] :=
    List.getElem?_eq_getElem hlen
  have hh : hex_nybble s.toList[2 * i] < 16 :=
    of_decide_eq_true (hok _ (List.getElem_mem (by omega)))
  have hl : hex_nybble s.toList[2 * i + 1] < 16 :=
    of_decide_eq_true (hok _ (List.getElem_mem hlen))
  unfold hex_byte_at
  simp [h0, h1, hi, hh, hl]

/-- Every byte of a dense, all-hex chunk list decodes.  This is the step
    that replaces evaluation over the payload: the chunk walk is an
    induction on the chunk list, and the per-byte work is
    `hex_byte_at_isSome`. -/
theorem segment_byte_at_isSome : ∀ (cs : List String),
    cs.all chunk_hex = true →
    ∀ (off : Nat), off < chunk_bytes cs → (segment_byte_at cs off).isSome = true
  | [], _, off, h => by
    simp [chunk_bytes] at h
  | s :: r, hok, off, h => by
    have hs : chunk_hex s = true :=
      (List.all_eq_true.mp hok) s (by simp)
    have hr : r.all chunk_hex = true :=
      List.all_eq_true.mpr
        (fun x hx => (List.all_eq_true.mp hok) x (by simp [hx]))
    have h' : off < s.length / 2 + chunk_bytes r := h
    simp only [segment_byte_at]
    by_cases hlt : off < s.length / 2
    · rw [ite_eq_left hlt]
      refine hex_byte_at_isSome ?_ hs
      have h2 := (Nat.lt_div_iff_mul_lt (by decide : 0 < 2)).mp hlt
      omega
    · rw [ite_eq_right hlt]
      exact segment_byte_at_isSome r hr (off - s.length / 2) (by omega)

/-- `find_segment` on a ONE-segment list, at an address that segment
    covers for a single byte. -/
theorem find_segment_single (seg : Segment) (x : Int)
    (h1 : (seg.seg_base : Int) ≤ x)
    (h2 : x + 1 ≤ (seg.seg_base : Int) + (seg.seg_size : Int)) :
    find_segment [seg] x 1 = some seg := by
  have hb : ((seg.seg_base : Int) ≤ x
      && x + 1 ≤ (seg.seg_base : Int) + (seg.seg_size : Int)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨by simpa using h1, by simpa using h2⟩
  show (if ((seg.seg_base : Int) ≤ x
      && x + 1 ≤ (seg.seg_base : Int) + (seg.seg_size : Int))
    then some seg else find_segment [] x 1) = some seg
  rw [ite_eq_left hb]

/-- `find_segment` at a byte the THIRD of three segments covers, the two
    earlier ranges missing it (the images' segments are disjoint). -/
theorem find_segment_third (a b c : Segment) (x : Int)
    (h1 : ¬ ((a.seg_base : Int) ≤ x ∧ x + 1 ≤ (a.seg_base : Int) + (a.seg_size : Int)))
    (h2 : ¬ ((b.seg_base : Int) ≤ x ∧ x + 1 ≤ (b.seg_base : Int) + (b.seg_size : Int)))
    (h3 : (c.seg_base : Int) ≤ x)
    (h4 : x + 1 ≤ (c.seg_base : Int) + (c.seg_size : Int)) :
    find_segment [a, b, c] x 1 = some c := by
  have hb1 : ((a.seg_base : Int) ≤ x
      && x + 1 ≤ (a.seg_base : Int) + (a.seg_size : Int)) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases hA : (a.seg_base : Int) ≤ x
    · right
      have hB : ¬ (x + 1 ≤ (a.seg_base : Int) + (a.seg_size : Int)) :=
        fun hB => h1 ⟨hA, hB⟩
      simpa using hB
    · left; simpa using hA
  have hb2 : ((b.seg_base : Int) ≤ x
      && x + 1 ≤ (b.seg_base : Int) + (b.seg_size : Int)) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases hA : (b.seg_base : Int) ≤ x
    · right
      have hB : ¬ (x + 1 ≤ (b.seg_base : Int) + (b.seg_size : Int)) :=
        fun hB => h2 ⟨hA, hB⟩
      simpa using hB
    · left; simpa using hA
  have hb3 : ((c.seg_base : Int) ≤ x
      && x + 1 ≤ (c.seg_base : Int) + (c.seg_size : Int)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨by simpa using h3, by simpa using h4⟩
  show (if ((a.seg_base : Int) ≤ x
      && x + 1 ≤ (a.seg_base : Int) + (a.seg_size : Int))
    then some a else find_segment [b, c] x 1) = some c
  rw [ite_eq_right (by rw [hb1]; simp)]
  show (if ((b.seg_base : Int) ≤ x
      && x + 1 ≤ (b.seg_base : Int) + (b.seg_size : Int))
    then some b else find_segment [c] x 1) = some c
  rw [ite_eq_right (by rw [hb2]; simp)]
  show (if ((c.seg_base : Int) ≤ x
      && x + 1 ≤ (c.seg_base : Int) + (c.seg_size : Int))
    then some c else find_segment [] x 1) = some c
  rw [ite_eq_left hb3]

/-- **The window lemma.**  A window `[lo, lo + N)` of a dense, writable
    segment is `wseg_ok`: every address in it resolves to that segment and
    finds a byte there.  This is the statement evaluation used to settle
    per image; see the section note above. -/
theorem wseg_ok_of_dense (segs : List Segment) (seg : Segment) (lo : word) (N : Nat)
    (Hnw : (lo.toNat : Int) + (N : Int) < ((2 ^ 64 : Nat) : Int))
    (Hfind : ∀ i : Nat, i < N →
      find_segment segs ((lo.toNat : Int) + (i : Int)) 1 = some seg)
    (Hwr : seg_writable seg = true)
    (Hdb : ∀ i : Nat, i < N →
      lo.toNat + i - seg.seg_base < chunk_bytes seg.seg_bytes)
    (Hdense : ∀ off : Nat, off < chunk_bytes seg.seg_bytes →
      (segment_byte_at seg.seg_bytes off).isSome = true) :
    wseg_ok segs lo N = true := by
  induction N generalizing lo with
  | zero => rfl
  | succ n ih =>
    have hn : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
    have hlt : (lo.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int) := by omega
    have hsucc : ((lo + 1).toNat : Int) = (lo.toNat : Int) + 1 := u_add1 lo hlt
    have hsuccN : (lo + 1).toNat = lo.toNat + 1 := by omega
    have hstep : wseg_ok segs lo (n + 1)
        = (match find_segment segs (lo.toNat : Int) 1 with
           | some sg =>
               (seg_writable sg &&
                 (match segment_byte_at sg.seg_bytes (lo.toNat - sg.seg_base) with
                  | some _ => true
                  | none => false) &&
                 wseg_ok segs (lo + 1) n)
           | none => false) := rfl
    rw [hstep]
    have h0 : find_segment segs (lo.toNat : Int) 1 = some seg := by
      have h := Hfind 0 (by omega)
      simpa using h
    have hb : (segment_byte_at seg.seg_bytes (lo.toNat - seg.seg_base)).isSome = true :=
      Hdense _ (Hdb 0 (by omega))
    have hbyte : (match segment_byte_at seg.seg_bytes (lo.toNat - seg.seg_base) with
        | some _ => true
        | none => false) = true := by
      cases h : segment_byte_at seg.seg_bytes (lo.toNat - seg.seg_base) with
      | none => rw [h] at hb; simp at hb
      | some b => rfl
    simp only [h0, Hwr, hbyte, Bool.true_and, Bool.and_true]
    refine ih (lo + 1) ?_ ?_ ?_
    · rw [hsucc]; omega
    · intro i hi
      have h := Hfind (i + 1) (by omega)
      rw [hsucc]
      rw [show ((lo.toNat : Int) + 1) + (i : Int)
          = (lo.toNat : Int) + ((i + 1 : Nat) : Int) from by push_cast; omega]
      exact h
    · intro i hi
      have h := Hdb (i + 1) (by omega)
      rw [hsuccN]
      rw [show lo.toNat + 1 + i = lo.toNat + (i + 1) from by omega]
      exact h

/- ######################################################################### -/
/- Store legality                                                            -/
/- ######################################################################### -/

/-- The source's one RWX segment covers `[0x10000, 0x11000)` (page-rounded)
    and carries a snapshot byte for every address of it, so `wview` is
    defined on all of them — both stores (`__environ` at `0x100e8`,
    `flag` at `0x100e4`) are legal. -/
theorem source_wseg : wseg_ok source_segs (0x10000 : word) 4096 = true := by
  have hcb : chunk_bytes SourceMemImage.SourceMemImage_segment_000.seg_bytes = 4096 := by
    decide
  have hok : SourceMemImage.SourceMemImage_segment_000.seg_bytes.all chunk_hex = true := by
    decide
  have hwr : seg_writable SourceMemImage.SourceMemImage_segment_000 = true := by decide
  have hloN : (0x10000 : word).toNat = 0x10000 := by decide
  have hloI : ((0x10000 : word).toNat : Int) = 0x10000 := by rw [hloN]; rfl
  have hfind : ∀ i : Nat, i < 4096 →
      find_segment source_segs ((0x10000 : word).toNat + (i : Int)) 1
        = some SourceMemImage.SourceMemImage_segment_000 := by
    intro i hi
    rw [hloI]
    show find_segment [SourceMemImage.SourceMemImage_segment_000]
      (0x10000 + (i : Int)) 1 = some SourceMemImage.SourceMemImage_segment_000
    refine find_segment_single _ _ ?_ ?_
    · show (0x10000 : Int) ≤ 0x10000 + (i : Int)
      omega
    · show 0x10000 + (i : Int) + 1 ≤ (0x10000 : Int) + 0x1000
      omega
  have hdb : ∀ i : Nat, i < 4096 →
      (0x10000 : word).toNat + i
        - SourceMemImage.SourceMemImage_segment_000.seg_base
        < chunk_bytes SourceMemImage.SourceMemImage_segment_000.seg_bytes := by
    intro i hi
    rw [hcb, hloN]
    show (0x10000 + i - 0x10000 : Nat) < 4096
    omega
  have hdense : ∀ off : Nat,
      off < chunk_bytes SourceMemImage.SourceMemImage_segment_000.seg_bytes →
      (segment_byte_at SourceMemImage.SourceMemImage_segment_000.seg_bytes off).isSome
        = true :=
    fun off hoff => segment_byte_at_isSome _ hok off hoff
  exact wseg_ok_of_dense source_segs SourceMemImage.SourceMemImage_segment_000
    (0x10000 : word) 4096 (by decide) hfind hwr hdb hdense

/-- The target's rw- data segment covers `[0x1002000, 0x1003000)`. -/
theorem target_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true := by
  have hcb : chunk_bytes TargetMemImage.TargetMemImage_segment_002.seg_bytes = 4096 := by
    decide
  have hok : TargetMemImage.TargetMemImage_segment_002.seg_bytes.all chunk_hex = true := by
    decide
  have hwr : seg_writable TargetMemImage.TargetMemImage_segment_002 = true := by decide
  have hloN : (0x1002000 : word).toNat = 0x1002000 := by decide
  have hloI : ((0x1002000 : word).toNat : Int) = 0x1002000 := by rw [hloN]; rfl
  have hfind : ∀ i : Nat, i < 4096 →
      find_segment target_segs ((0x1002000 : word).toNat + (i : Int)) 1
        = some TargetMemImage.TargetMemImage_segment_002 := by
    intro i hi
    rw [hloI]
    show find_segment [TargetMemImage.TargetMemImage_segment_000,
        TargetMemImage.TargetMemImage_segment_001,
        TargetMemImage.TargetMemImage_segment_002] (0x1002000 + (i : Int)) 1
      = some TargetMemImage.TargetMemImage_segment_002
    refine find_segment_third _ _ _ _
      (by show ¬ ((0x1000000 : Int) ≤ 0x1002000 + (i : Int)
            ∧ 0x1002000 + (i : Int) + 1 ≤ (0x1000000 : Int) + 0x1000); omega)
      (by show ¬ ((0x1001000 : Int) ≤ 0x1002000 + (i : Int)
            ∧ 0x1002000 + (i : Int) + 1 ≤ (0x1001000 : Int) + 0x1000); omega)
      (by show (0x1002000 : Int) ≤ 0x1002000 + (i : Int); omega)
      (by show 0x1002000 + (i : Int) + 1 ≤ (0x1002000 : Int) + 0x1000; omega)
  have hdb : ∀ i : Nat, i < 4096 →
      (0x1002000 : word).toNat + i
        - TargetMemImage.TargetMemImage_segment_002.seg_base
        < chunk_bytes TargetMemImage.TargetMemImage_segment_002.seg_bytes := by
    intro i hi
    rw [hcb, hloN]
    show (0x1002000 + i - 0x1002000 : Nat) < 4096
    omega
  have hdense : ∀ off : Nat,
      off < chunk_bytes TargetMemImage.TargetMemImage_segment_002.seg_bytes →
      (segment_byte_at TargetMemImage.TargetMemImage_segment_002.seg_bytes off).isSome
        = true :=
    fun off hoff => segment_byte_at_isSome _ hok off hoff
  exact wseg_ok_of_dense target_segs TargetMemImage.TargetMemImage_segment_002
    (0x1002000 : word) 4096 (by decide) hfind hwr hdb hdense

/-- Every store into the source's writable window is legal, for EVERY
    memory: the segment fallback supplies the bytes, and the overlay can
    only override them with other bytes. -/
theorem source_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : (0x10000 : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (0x11000 : Int)) :
    store_ok source_segs m a n = true := by
  refine store_ok_window source_segs m (0x10000 : word) a 4096 n 0x10000 0x11000
    (by decide) (by decide) (by decide) source_wseg ?_ ?_
  · simpa using Hlo
  · simpa using Hhi

/-- And every store into the target's `.data` window. -/
theorem target_store_ok (m : word → Option byte) (a : word) (n : Nat)
    (Hlo : (0x1002000 : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (0x1003000 : Int)) :
    store_ok target_segs m a n = true := by
  refine store_ok_window target_segs m (0x1002000 : word) a 4096 n 0x1002000 0x1003000
    (by decide) (by decide) (by decide) target_wseg ?_ ?_
  · simpa using Hlo
  · simpa using Hhi

end LinuxSem.Examples.RwxFlagNs

namespace LinuxSem.Examples.RwxFlagNs.RwxFlagNsDefs

theorem TD_10011a0 :
    decodeAny 0x05d00893 = some (Instr.opImm .ADD 0x11#5 0x00#5 0x05d#12, 4) := by
  decide

end LinuxSem.Examples.RwxFlagNs.RwxFlagNsDefs

