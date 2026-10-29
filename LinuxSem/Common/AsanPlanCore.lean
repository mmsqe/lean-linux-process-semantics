/-
  * Common.AsanPlanCore — the reflective ASan plan checker WITHOUT the plan
    syntax / dispatch / `check` .
  `APC`.  Read `AxSymExec3.lean`'s header first (`AX2`) and then
  `AxSymExec3B.lean`'s (`AX2B`): this file is the plan checker built on both.
 A plan is a deep-embedded
  itinerary, `check` runs it with `vm_compute` / `native_compute` and returns
  the SHAPE (trace-set skeleton, with named HOLES for hand-off to other
  certificates), and `AsanPlanSound.check_sound` turns `check ... cs p = COk s`
  into `realizes` for every concrete configuration the checker state `cs`
  describes (`AsanPlanSound.cs_ok`).
  Design:
  * EVERY node is a BOUNDARY node (applies to the current state without
    running); running a block is the explicit node `PRun stops k` (run the
    executor until an ecall / a STOP pc / an undecidable instruction, carry
    the store log into the knowledge, GC, continue with `k`).  So a syscall
    node is written `PRun [] (PSys YMmap k)`, a summary call
    `PRun [] (PX XMemset [] k)`, an abstraction in the middle of straight
    code `PRun [pc] (PFresh r 16 k)`.
  * the MODEL part of the state tracks the mmap ledger `vm_maps` EXACTLY
    (`a_maps`, newest first, each entry with a KIND hint: rw eager / rw lazy
    (MAP_NORESERVE) / PROT_NONE reservation (eager or lazy)), numeric upper
    bounds for the gap lemma (`a_totsz`), the placement split (`a_ylo`), the
    eagerly backed bytes (`a_eager`), the ALLOWED lazy intervals (`a_vis`,
    see AsanAcct: blocks run on the RESTRICTED memory that hides every lazy
    byte outside the allowed pages, so the executor itself knows nothing
    about page accounting) and their byte bound (`a_abytes`), the program
    break (`a_brk`), the fd table (`a_fd`) and whether set_tid_address ran.
  * syscall nodes `PSys`: mmap arms P/A/B0/B (NULL hint), C/C0/D/D0 (FIXED,
    free), E/F/G (FIXED inside a tracked entry), munmap (exact entry), brk
    query / provably blocked grow, set_tid_address; `PBrk2` = brk grow with
    both outcomes; `PExit`.  Every memory syscall has a REFUSED child
    (`node_mmap2` / `node_mmapin` (3 resolutions) / `node_mprotect2`);
    `node_spin` is the sealed runtime's self-loop leaf.
    The checker verifies the budget / gap slack numerically.
  * abstraction / bookkeeping nodes: `PFresh` (re-spell a register as a
    scaled fresh variable c*v), `PFact` (add a fact the checker can verify),
    `PForget` (drop knowledge), `PSplit`/`PContra`.  Lazy rw maps are
    visible wholesale: their bytes are visible, zero and writable.
  * extension nodes `PX x args`: routine summaries (internal_memset,
    internal_memcpy, musl memset, mem_is_zero) and the two musl start-up
    loops over the (hidden) argument block (envp count, program-name scan),
    plus `XLayout` facts about the initial stack image.  Each has ONE
    soundness obligation (AsanPlanSound, Section hypotheses).
  * hand-off leaves `PHandoff h`: the current state must syntactically
    ENTAIL the stored state `HS h` (a parameter of `check`); shape `SHole h`.
  Conventions: aligned unknowns are spelled as SCALED variables (sp = 16*s,
  a NULL-hint grant = 4096*m, ...), so shifts and masks on them are exact
  linear operations for the executor.  All expressions the checker builds go
  through the executor's smart constructors (`mkAlu`/`mkMd`) so that they are
  in the same normal form as the executor's own values.
  Computational part only (this file); proofs in AsanPlanSound.
  `KFill` cases are everywhere (treated like KZero); `summary_fill` emits
  `KFill` for nonzero fill bytes.
 Nothing is
  deferred; `lake env lean LinuxSem/Common/AsanPlanCore.lean`
  is silent.  In particular the `..B`-vs-reference equalities of the whole
  file are PROVED here (`kentry_apart_bB_eqf` .. `summary_sniff_eq`,
  `run_block_eq`, `cs_gc_eq`), not assumed, and the `by decide` smoke tests
  at the end pin the decidable definitions.
  - `1`   shapes (`spiece`, `shape`, `salt2`, the `*_eqb`s).
  - `2`   checker state (`mkind`, `amap`, `afd`, `acs`, accessors,
          expression builders).
  - `3`   running a block + knowledge GC (`expr_vars`/`live_vars`,
          `kn_gc_entry`, `cs_gc_ref`, the trie `.._t` versions, `cs_gc`,
          and the whole `cs_gc = cs_gc_ref` agreement chain).
  - `4`   variable hygiene (`expr_vars_lt` .. `fresh_ok`) and the two block
          runners `run_block_ref` / `run_block` (+ `run_block_gc`).
  - `5`   knowledge utilities: apartness/fill/havoc/cut-out families with
          their `..B` twins and `.._eqf` lemmas, `kn_keep`, `kimg_cut*`,
          `kreadZ`/`kread8e`/`kread_bytes`, `kwritable*`, `kzero_x`,
          `kfill_x`, `off_image_x`, `flat_x`, `len_eqb`, `page_aligned`,
          `kn_contra`.
  - `6`   registers after a call (`caller_saved`, `sr_fresh`, `NCS`,
          `ret_lit`, `after_call`, `after_call2`).
  - `8`   the node checkers: split/fact/forget/fresh, visible ranges and
          shadows, mmap (null/fixed/fixed-in/destroyed), mprotect, munmap,
          brk, set_tid_address/exit, fog/ghost/unvis/spin, the routine
          summaries (fill/copy/mem_is_zero/istrncpy/popfree/sniff), the
          initial-variable conventions and `XLayout`, hand-off entailment,
          loops (`esubst`/`inst`/`entails_h`/`loop_ok`), diamonds, `PVia`,
          cell abstraction, re-spelling, word havoc.
  - `9`   `STOPS` and the partial instruction table `mk_itab_ranges`.
  - `9b`  the initial checker state of an image (`init_kn*`, `init_acs_of*`).
  - `10`  the address tables `ASAN` / `BOTH` and their initial states.
  - plus `## Sanity checks` (`by decide`).
  NOTES.
  - Lean HAS no section variables inserted at USE sites (only at declaration
    sites), so — as in `AxSymExec3B` — the `Section WithSegs`
    context is threaded EXPLICITLY: every definition that needs part of
    `segs IT A nx0 LIMIT` takes it as leading explicit parameters in that
    fixed order, and call sites pass them (`run_block segs IT nx0 K fuel
    stops cs`, `mmap_null A nx0 LIMIT cs kind eager visible`, ...).  The
    `section WithSegs` remains only as this tree's grouping device.
  - `carryK` (the GROUPED vertical carry) is NOT declared in this tree's
    `AxSymExec3B` (see that file's header); `run_block` therefore calls
    `carryK0`, which `AxSymExec3B.carryK0_eq` proves equal to the reference
    `carry`.  `run_block_eq` uses exactly that equality.
  - `Z` is `Int`, `nat` is `Nat`, `positive` ids are `Nat`; `fst`/`snd` are
    `.1`/`.2`; `×` is right-associative .
  - `if b then x else y` on a `Bool` stays `if b then x else y`; `Z.leb` /
    `Z.ltb` / `Z.eqb` become `≤` / `<` / `==`; `negb` is `!`;
    `existsb`/`forallb` are `List.any`/`List.all`; `List.find` is
    `List.find?`; `seq 0 n` is `List.range n`; `Z.of_nat n` is `(n : Int)`;
    `Z.to_nat` is `.toNat`; `2 ^ k` (on `Z`) is `zpow 2 k`; `Z.log2` is
    `zlog2` (`AxSymExec3`); `Z.land` is `zland`.
  - a `match ... end` that  concatenates with `&&` is parenthesized
    explicitly here (Lean's `match` swallows what follows it).
  - `List.Forall` does not exist in this core: the "for all members"
    side conditions are `∀ x ∈ l, P x` (none occur in this file).
  - Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AxSymExec3B
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanPlanCore

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3B

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! ## 0. Constants and the address table (one instance per image) -/

/-- `AsanCeil.alloc_ceiling`: every grant ends below it; the stack window and
    the argument block lie above it. -/
def CEIL : Int := 0x7fff7f800000

/-- `AsanPlacement.kHighMemBeg`: NULL-hint grants land strictly above it, every
    other ledger interval (image, shadows, brk heap) ends at or below it. -/
def KHI : Int := 0x10007fff8000

/-- `AsanCeil.bottomup_floor`. -/
def FLOOR : Int := 0x2aaaaaaab000

/-- `State.mmap_base_min` (initial value of `a_ylo`). -/
def MBASE_MIN : Int := 0x154555557000

/-- set_tid_address: the tid is in (0, PID_MAX_ENVELOPE). -/
def PID_MAX : Int := 4194304

/-- The per-image address table. -/
structure atable where
  /-- the loaded image hull `[img_lo, img_hi)` (all segments inside, contiguous) -/
  img_lo : Int
  img_hi : Int
  /-- number of reserved ledger intervals (= length (segments_reserved segs)) -/
  n_res : Nat
  /-- ASan shadow offset: shadow(a) = a/8 + shadow_off -/
  shadow_off : Int
  /-- entry pc (_start) -/
  a_entry : Int
  /-- the writable window of the image `[rw_lo, rw_lo+rw_len)` (.data .. end of .bss, contiguous) -/
  rw_lo : Int
  rw_len : Int
  /-- the auxv values AT_PHDR / AT_PHENT / AT_PHNUM of the image -/
  ph_addr_z : Int
  ph_ent_z : Int
  ph_num_z : Int
  /-- summarized routines (entry pcs; also resume stops) -/
  x_imemset : Int
  x_imemcpy : Int
  x_memset : Int
  x_memcpy : Int
  x_memiszero : Int
  /-- sanitizer internal_strncpy entry + the address of the 9 image bytes "<sealed>\0" (its only source),
      SizeClassAllocator64 PopulateFreeArray fill-loop head (exit = head + 32) — NOT in `STOPS`: plans stop there explicitly -/
  x_istrncpy : Int
  x_sealed : Int
  x_popfree : Int
  /-- pni_sniff_header entry (the library call, summarized by `summary_sniff`), its 16-byte jump table in .rodata
      and the .bss cell holding the shadow base it loads -/
  x_sniff : Int
  sniff_tab : Int
  sniff_cell : Int
  /-- musl __init_libc: envp-counting loop head / exit, program-name scan loop head / exit -/
  x_envscan : Int
  x_envscan_k : Int
  x_pnscan : Int
  x_pnscan_k : Int
  /-- further resume stops -/
  stops_more : List Int
  deriving DecidableEq, Repr

section WithSegs
open atable

-- THE CONTEXT, threaded EXPLICITLY (Lean section variables are not inserted
-- at use sites, so — as in `AxSymExec3B` — every definition that needs part of
-- the context takes it as leading explicit parameters, in the fixed order
-- `segs`, `IT`, `A`, `nx0`, `LIMIT`):
--   `segs`  the image's segments,
--   `IT`    the decoded-instruction table,
--   `A`     the address table,
--   `nx0`   variables below it are the INITIAL ones (splits / shapes may only
--           mention those),
--   `LIMIT` the run's backing budget (vm_limit): target_alloc_limit.

/-! ## 1. Shapes -/

/-- pieces of an emitted byte string: literal bytes, or the value of a
    byte-string variable `eb E k` (the convention: k = 0 file content,
    1 argv[0], 2 argv[1]) -/
inductive spiece : Type
  | SPLit (bs : List Int)
  | SPBlob (k : Nat)
  deriving DecidableEq, Repr

/-- The shape of what a plan emits: a trace-set skeleton. -/
inductive shape : Type
  | SNil
  | SExit (code : Int)
  /-- the writes of the pieces' bytes to fd, then s -/
  | SEmitP (fd : Int) (ps : List spiece) (s : shape)
  | SAlt2 (a b : shape)
  | SCase (e : expr) (mid : Int) (s1 s2 : shape)
  /-- hand-off to certificate/lemma number h -/
  | SHole (h : Nat)
  /-- inside a loop body: the next iteration (leaf `PNext`) -/
  | SNext
  deriving DecidableEq, Repr

/-- `salt2`. -/
def salt2 (a b : shape) : shape :=
  match a, b with
  | .SNil, _ => b
  | _, .SNil => a
  | _, _ => .SAlt2 a b

/-- Boolean equality of literal byte lists. -/
def listZ_eqb : List Int → List Int → Bool
  | [], [] => true
  | a :: x', b :: y' => (a == b) && listZ_eqb x' y'
  | _, _ => false

/-- Boolean equality of pieces. -/
def spiece_eqb (x y : spiece) : Bool :=
  match x, y with
  | .SPLit a, .SPLit b => listZ_eqb a b
  | .SPBlob k, .SPBlob k' => k == k'
  | _, _ => false

/-- Boolean equality of piece lists. -/
def spieces_eqb : List spiece → List spiece → Bool
  | [], [] => true
  | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y'
  | _, _ => false

/-- Boolean equality of shapes. -/
def shape_eqb : shape → shape → Bool
  | .SNil, .SNil => true
  | .SExit c, .SExit c' => c == c'
  | .SEmitP fd ps s, .SEmitP fd' ps' s' => (fd == fd') && spieces_eqb ps ps' && shape_eqb s s'
  | .SAlt2 a b, .SAlt2 a' b' => shape_eqb a a' && shape_eqb b b'
  | .SCase e m a b, .SCase e' m' a' b' =>
      expr_eqb e e' && (m == m') && shape_eqb a a' && shape_eqb b b'
  | .SHole h, .SHole h' => h == h'
  | .SNext, .SNext => true
  | _, _ => false

/-! ## 2. Checker state -/

/-- Kind of a tracked ledger entry (a HINT selecting the admissible
    operations; only `KRWLAZY` carries a semantic invariant: every byte of the
    entry is outside `vm_noaccess` and on a lazy page).  `KHOLE` = a provably
    FREE range (see `is_hole`). -/
inductive mkind : Type
  | KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE
  deriving DecidableEq, Repr

/-- Boolean equality of ledger kinds. -/
def mkind_eqb (a b : mkind) : Bool :=
  match a, b with
  | .KRW, .KRW | .KRWLAZY, .KRWLAZY | .KNONE, .KNONE | .KNONELAZY, .KNONELAZY
  | .KFOG, .KFOG | .KHOLE, .KHOLE => true
  | _, _ => false

/-- One tracked ledger entry (vm_maps element), in LEDGER ORDER (newest first):
    the model's entry is exactly `(den am_base, den am_len)`. -/
structure amap where
  /-- page aligned -/
  am_base : expr
  /-- the page-rounded length (its value) -/
  am_len : expr
  am_kind : mkind
  deriving DecidableEq, Repr

/-- fog: an `a_maps` element of kind `KFOG` is a TOKEN standing for ZERO OR ONE
    untracked `vm_maps` entry of size at most `am_len` at that list position
    (the musl start-up allocation variants); it is not a mapping: every lookup
    below skips it.

    an element of kind `KHOLE` is a TOKEN too: it stands for NO entry and
    records that the range `am_base, +am_len` is FREE (no reserved or mapped
    interval meets it) — the hole a refused-DESTROYED `PMmapInH` punched into
    a tracked entry; a later MAP_FIXED over exactly that range is a fresh grant
    (`mmap_fixed_free`, hole path).  NULL-hint grants may land inside a hole,
    so `mmap_null` refuses while a hole exists.  `is_fog` is token-ness (fog
    OR hole): every lookup of a real mapping skips both; `is_hole` tells them
    apart. -/
def is_tok_kind (k : mkind) : Bool :=
  match k with | .KFOG | .KHOLE => true | _ => false

/-- Is the ledger entry a hole token? -/
def is_hole (m : amap) : Bool := mkind_eqb m.am_kind .KHOLE

/-- Is the ledger entry a token (fog or hole)? -/
def is_fog (m : amap) : Bool := is_tok_kind m.am_kind

/-- No fog token in the ledger. -/
def no_fog (ms : List amap) : Bool := ms.all (fun m => !is_fog m)

/-- No hole token in the ledger. -/
def no_holes (ms : List amap) : Bool := ms.all (fun m => !is_hole m)

/-- Open-file state of fd 3 (the only file the driver opens). -/
inductive afd : Type
  /-- fds 0,1,2 only -/
  | FdStd
  /-- + fd 3 = regular file: 64 KiB chunk j of its content is blob k+j,
      len = min(content length, 2^26), off = current offset -/
  | FdFile (k : Nat) (len off : expr)
  /-- + fd 3 = a directory -/
  | FdDir
  deriving DecidableEq, Repr

/-- The checker state. -/
structure acs where
  /-- pc, regs, EMPTY log, knowledge, next var -/
  a_ss : sym_state
  /-- = vm_maps, exactly, newest first -/
  a_maps : List amap
  /-- >= Σ over reserved ++ maps of the interval sizes [gap lemma] -/
  a_totsz : Int
  /-- <= the ledger_split high mark Y (top-down placement bound) -/
  a_ylo : Int
  /-- >= eager_used model -/
  a_eager : Int
  /-- VISIBLE APPLICATION RANGES (base, len), both multiples of 8: their
      ASan shadows `shadow_off + base/8, + len/8` are the allowed lazy
      bytes (plus the ranges themselves when they are lazy rw maps) -/
  a_vis : List (expr × expr)
  /-- formerly visible ranges (munmapped): still budgeted (their shadow
      pages may be materialized) but no longer visible -/
  a_ghost : List (expr × expr)
  /-- >= A_bytes of the page-rounded ranges + shadows (a_vis ++ a_ghost) -/
  a_abytes : Int
  /-- = vm_brk -/
  a_brk : expr
  a_fd : afd
  /-- set_tid_address done -/
  a_tidset : Bool
  deriving DecidableEq, Repr

/-- `AM` — the ledger-entry constructor. -/
abbrev AM (b l : expr) (k : mkind) : amap := ⟨b, l, k⟩

/-- `ACS` — the checker-state constructor. -/
abbrev ACS (ss : sym_state) (ms : List amap) (totsz ylo eager : Int)
    (vis ghost : List (expr × expr)) (abytes : Int) (brk : expr) (fd : afd)
    (tidset : Bool) : acs :=
  ⟨ss, ms, totsz, ylo, eager, vis, ghost, abytes, brk, fd, tidset⟩

open acs in
/-- Register `n` of the state (`ELit 0` if out of range). -/
def reg (cs : acs) (n : Nat) : expr := (cs.a_ss.s_regs.getD n (.ELit 0))

/-- The state's knowledge. -/
def kn (cs : acs) : List kentry := cs.a_ss.s_know

/-- The state's pc. -/
def pc (cs : acs) : Int := cs.a_ss.s_pc

/-- The state's next-variable counter. -/
def nxt (cs : acs) : Nat := cs.a_ss.s_next

/-- Replace the symbolic state, keeping the model part. -/
def with_ss (cs : acs) (ss : sym_state) : acs :=
  ⟨ss, cs.a_maps, cs.a_totsz, cs.a_ylo, cs.a_eager, cs.a_vis, cs.a_ghost,
   cs.a_abytes, cs.a_brk, cs.a_fd, cs.a_tidset⟩

/-- A clean symbolic state with no log and no reservation. -/
def mk_ss (p : Int) (sr : List expr) (k : List kentry) (nx : Nat) : sym_state :=
  ⟨p, sr, [], k, nx, none⟩

/-- Write a register. -/
def set_reg (cs : acs) (n : Nat) (e : expr) : acs :=
  let ss := cs.a_ss
  with_ss cs (mk_ss ss.s_pc (sr_upd ss.s_regs n e) ss.s_know ss.s_next)

/-- Set the pc. -/
def set_pc (cs : acs) (p : Int) : acs :=
  let ss := cs.a_ss
  with_ss cs (mk_ss p ss.s_regs ss.s_know ss.s_next)

/-- Replace the knowledge. -/
def set_kn (cs : acs) (k : List kentry) : acs :=
  let ss := cs.a_ss
  with_ss cs (mk_ss ss.s_pc ss.s_regs k ss.s_next)

/-- Prepend knowledge. -/
def add_kn (cs : acs) (k : List kentry) : acs := set_kn cs (k ++ kn cs)

/-- Bump the next-variable counter. -/
def bump (cs : acs) (d : Nat) : acs :=
  let ss := cs.a_ss
  with_ss cs (mk_ss ss.s_pc ss.s_regs ss.s_know (ss.s_next + d))

/-- Replace the register file. -/
def set_regs (cs : acs) (sr : List expr) : acs :=
  let ss := cs.a_ss
  with_ss cs (mk_ss ss.s_pc sr ss.s_know ss.s_next)

/-- The literal value of an expression, if it is one. -/
def lit_of (e : expr) : Option Int :=
  match e with | .ELit z => some (z % two64) | _ => none

/-- The literal value of a register, if it is one. -/
def reg_lit (cs : acs) (n : Nat) : Option Int := lit_of (reg cs n)

/-! ### Expression builders (normal forms of the executor) -/

/-- `a + b`. -/
def eadd (a b : expr) : expr := mkAlu .ADD a b

/-- `a - b`. -/
def esub (a b : expr) : expr := mkAlu .SUB a b

/-- `c * e`. -/
def escale (c : Int) (e : expr) : expr := mkMd .MUL (.ELit c) e

/-- `a + z`. -/
def eaddz (a : expr) (z : Int) : expr := mkAlu .ADD a (.ELit z)

/-! ## 3. Running a block + knowledge GC -/

/-- Knowledge GC (a pure weakening): drop memory facts about stack cells
    strictly below the stack pointer (dead frames) and pure facts all of whose
    variables are dead (mentioned by no register, memory fact, map, allow
    interval or brk, and not initial). -/
def expr_vars : expr → List Nat → List Nat
  | .ELit _, acc => acc
  | .EVar n, acc => if acc.any (fun v => n == v) then acc else n :: acc
  | .EAlu _ x y, acc => expr_vars x (expr_vars y acc)
  | .EAluw _ x y, acc => expr_vars x (expr_vars y acc)
  | .EMd _ x y, acc => expr_vars x (expr_vars y acc)
  | .EMdw _ x y, acc => expr_vars x (expr_vars y acc)
  | .EExt _ _ _ x, acc => expr_vars x acc
  | .EBlob _ _ _ _, acc => acc

/-- The live variables of the state. -/
def live_vars (cs : acs) : List Nat :=
  let acc := cs.a_ss.s_regs.foldr expr_vars []
  let acc := (kn cs).foldr (fun K acc =>
    match K with
    | .KWord a _ v => expr_vars a.a_base (expr_vars v acc)
    | .KZero a n => expr_vars a.a_base (expr_vars n acc)
    | .KBlob a n _ => expr_vars a.a_base (expr_vars n acc)
    | .KWr a n => expr_vars a.a_base (expr_vars n acc)
    | .KFill a n _ => expr_vars a.a_base (expr_vars n acc)
    | .KUnk a n => expr_vars a.a_base (expr_vars n acc)
    | _ => acc) acc
  let acc := cs.a_maps.foldr (fun m acc => expr_vars m.am_base (expr_vars m.am_len acc)) acc
  let acc := cs.a_vis.foldr (fun p acc => expr_vars p.1 (expr_vars p.2 acc)) acc
  let acc := cs.a_ghost.foldr (fun p acc => expr_vars p.1 (expr_vars p.2 acc)) acc
  let acc := match cs.a_fd with
    | .FdFile _ l o => expr_vars l (expr_vars o acc)
    | _ => acc
  expr_vars cs.a_brk acc

/-- All variables of `e` are live (or initial). -/
def all_live (nx0 : Nat) (live : List Nat) (e : expr) : Bool :=
  (expr_vars e []).all (fun v => v < nx0 || live.any (fun x => v == x))

/-- Does the GC keep this knowledge entry? -/
def kn_gc_entry (nx0 : Nat) (spb : expr) (spk : Int) (live : List Nat) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, k⟩ w _ => !(expr_eqb b spb && (k + (w : Int) ≤ spk))
  | .KZero ⟨b, k⟩ (.ELit n) => !(expr_eqb b spb && (k + n ≤ spk))
  | .KBlob ⟨b, k⟩ (.ELit n) _ => !(expr_eqb b spb && (k + n ≤ spk))
  | .KFill ⟨b, k⟩ (.ELit n) _ => !(expr_eqb b spb && (k + n ≤ spk))
  | .KUnk ⟨b, k⟩ (.ELit n) => !(expr_eqb b spb && (k + n ≤ spk))
  | .KRange e _ _ => all_live nx0 live e
  | .KAlign e _ => all_live nx0 live e
  | .KDisj a1 n1 a2 n2 =>
      all_live nx0 live a1.a_base && all_live nx0 live n1
      && all_live nx0 live a2.a_base && all_live nx0 live n2
  | _ => true

/-- The reference GC. -/
def cs_gc_ref (nx0 : Nat) (cs : acs) : acs :=
  let (spb, spk) := split_lit (reg cs 2)
  let live := live_vars cs
  set_kn cs ((kn cs).filter (kn_gc_entry nx0 spb spk live))

/-- PERF: the live set as a trie (variable indices are unary `Nat`s; list
    membership by `==` against hundreds of live variables, for every variable
    occurrence, was several percent of a leaf).  `cs_gc_eq`: equal to
    `cs_gc_ref`. -/
def vkey (n : Nat) : Nat := n + 1

/-- The trie insertion key is injective. -/
theorem vkey_inj {a b : Nat} (h : vkey a = vkey b) : a = b := by
  simp only [vkey] at h
  omega

/-- The trie-collecting walk. -/
def expr_vars_t : expr → ptree Unit → ptree Unit
  | .ELit _, acc => acc
  | .EVar n, acc => pt_set (vkey n) () acc
  | .EAlu _ x y, acc => expr_vars_t x (expr_vars_t y acc)
  | .EAluw _ x y, acc => expr_vars_t x (expr_vars_t y acc)
  | .EMd _ x y, acc => expr_vars_t x (expr_vars_t y acc)
  | .EMdw _ x y, acc => expr_vars_t x (expr_vars_t y acc)
  | .EExt _ _ _ x, acc => expr_vars_t x acc
  | .EBlob _ _ _ _, acc => acc

/-- The state's live set as a trie. -/
def live_vars_t (cs : acs) : ptree Unit :=
  let acc := cs.a_ss.s_regs.foldr expr_vars_t (.PTLeaf : ptree Unit)
  let acc := (kn cs).foldr (fun K acc =>
    match K with
    | .KWord a _ v => expr_vars_t a.a_base (expr_vars_t v acc)
    | .KZero a n => expr_vars_t a.a_base (expr_vars_t n acc)
    | .KBlob a n _ => expr_vars_t a.a_base (expr_vars_t n acc)
    | .KWr a n => expr_vars_t a.a_base (expr_vars_t n acc)
    | .KFill a n _ => expr_vars_t a.a_base (expr_vars_t n acc)
    | .KUnk a n => expr_vars_t a.a_base (expr_vars_t n acc)
    | _ => acc) acc
  let acc := cs.a_maps.foldr (fun m acc => expr_vars_t m.am_base (expr_vars_t m.am_len acc)) acc
  let acc := cs.a_vis.foldr (fun p acc => expr_vars_t p.1 (expr_vars_t p.2 acc)) acc
  let acc := cs.a_ghost.foldr (fun p acc => expr_vars_t p.1 (expr_vars_t p.2 acc)) acc
  let acc := match cs.a_fd with
    | .FdFile _ l o => expr_vars_t l (expr_vars_t o acc)
    | _ => acc
  expr_vars_t cs.a_brk acc

/-- Trie membership. -/
def in_live_t (t : ptree Unit) (v : Nat) : Bool :=
  match pt_get t (vkey v) with | some _ => true | none => false

/-- The trie variant of `all_live`. -/
def expr_all_live_t (nx0 : Nat) : ptree Unit → expr → Bool
  | t, .ELit _ => true
  | t, .EVar n => if n < nx0 then true else in_live_t t n
  | t, .EAlu _ x y => if expr_all_live_t nx0 t x then expr_all_live_t nx0 t y else false
  | t, .EAluw _ x y => if expr_all_live_t nx0 t x then expr_all_live_t nx0 t y else false
  | t, .EMd _ x y => if expr_all_live_t nx0 t x then expr_all_live_t nx0 t y else false
  | t, .EMdw _ x y => if expr_all_live_t nx0 t x then expr_all_live_t nx0 t y else false
  | t, .EExt _ _ _ x => expr_all_live_t nx0 t x
  | t, .EBlob _ _ _ _ => true

/-- The trie variant of `kn_gc_entry`. -/
def kn_gc_entry_t (nx0 : Nat) (spb : expr) (spk : Int) (t : ptree Unit) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, k⟩ w _ => !(expr_eqb b spb && (k + (w : Int) ≤ spk))
  | .KZero ⟨b, k⟩ (.ELit n) => !(expr_eqb b spb && (k + n ≤ spk))
  | .KBlob ⟨b, k⟩ (.ELit n) _ => !(expr_eqb b spb && (k + n ≤ spk))
  | .KFill ⟨b, k⟩ (.ELit n) _ => !(expr_eqb b spb && (k + n ≤ spk))
  | .KUnk ⟨b, k⟩ (.ELit n) => !(expr_eqb b spb && (k + n ≤ spk))
  | .KRange e _ _ => expr_all_live_t nx0 t e
  | .KAlign e _ => expr_all_live_t nx0 t e
  | .KDisj a1 n1 a2 n2 =>
      expr_all_live_t nx0 t a1.a_base && expr_all_live_t nx0 t n1
      && expr_all_live_t nx0 t a2.a_base && expr_all_live_t nx0 t n2
  | _ => true

/-- The GC through the trie. -/
def cs_gc (nx0 : Nat) (cs : acs) : acs :=
  let (spb, spk) := split_lit (reg cs 2)
  let live := live_vars_t cs
  set_kn cs ((kn cs).filter (kn_gc_entry_t nx0 spb spk live))

/-! ### `cs_gc = cs_gc_ref` -/

/-- The list representation and the trie representation agree. -/
def live_agree (acc : List Nat) (t : ptree Unit) : Prop :=
  ∀ v, acc.any (fun x => v == x) = in_live_t t v

/-- `live_agree` is preserved by inserting a variable on both sides. -/
theorem live_agree_var {acc : List Nat} {t : ptree Unit} {n : Nat} (H : live_agree acc t) :
    live_agree (if acc.any (fun x => n == x) then acc else n :: acc)
      (pt_set (vkey n) () t) := by
  intro v
  by_cases hvn : v = n
  · subst hvn
    have hL : in_live_t (pt_set (vkey v) () t) v = true := by
      simp only [in_live_t, pt_gss]
    rw [hL]
    by_cases h : acc.any (fun x => v == x)
    · simp [h]
    · simp [h]
  · have hk : vkey v ≠ vkey n := fun hh => hvn (vkey_inj hh)
    have hR : in_live_t (pt_set (vkey n) () t) v = in_live_t t v := by
      simp only [in_live_t, pt_gso (vkey v) (vkey n) () t hk]
    rw [hR, ← H v]
    by_cases h : acc.any (fun x => n == x)
    · simp only [h, ite_true]
    · simp only [h, ite_false, List.any_cons]
      have hb : (v == n) = false := by
        simpa using hvn
      simp [hb]

/-- `live_agree` is preserved by the variable-collecting walk. -/
theorem live_agree_expr (e : expr) :
    ∀ acc t, live_agree acc t → live_agree (expr_vars e acc) (expr_vars_t e t) := by
  induction e with
  | ELit z => intro acc t H; exact H
  | EVar n => intro acc t H; exact live_agree_var H
  | EAlu op a b iha ihb => intro acc t H; exact iha _ _ (ihb _ _ H)
  | EAluw op a b iha ihb => intro acc t H; exact iha _ _ (ihb _ _ H)
  | EMd op a b iha ihb => intro acc t H; exact iha _ _ (ihb _ _ H)
  | EMdw op a b iha ihb => intro acc t H; exact iha _ _ (ihb _ _ H)
  | EExt sx lo n a iha => intro acc t H; exact iha _ _ H
  | EBlob sx k i n => intro acc t H; exact H

/-- `live_agree` is preserved by a fold of the walk. -/
theorem live_agree_fold {X : Type} (f : X → List Nat → List Nat)
    (g : X → ptree Unit → ptree Unit) (l : List X) :
    ∀ acc t, (∀ (a : X) (acc : List Nat) (t : ptree Unit),
                live_agree acc t → live_agree (f a acc) (g a t)) →
      live_agree acc t → live_agree (l.foldr f acc) (l.foldr g t) := by
  induction l with
  | nil => intro acc t _ H; exact H
  | cons a r ih => intro acc t Hfg H; exact Hfg a _ _ (ih acc t Hfg H)

/-- `live_vars` and `live_vars_t` agree. -/
theorem live_vars_agree (nx0 : Nat) (cs : acs) : live_agree (live_vars cs) (live_vars_t cs) := by
  have A0 : live_agree ([] : List Nat) (ptree.PTLeaf : ptree Unit) := by
    intro v
    simp only [List.any_nil, in_live_t, pt_get_leaf]
  have hfd : ∀ acc t, live_agree acc t →
      live_agree (match cs.a_fd with
                  | .FdFile _ l o => expr_vars l (expr_vars o acc)
                  | _ => acc)
                 (match cs.a_fd with
                  | .FdFile _ l o => expr_vars_t l (expr_vars_t o t)
                  | _ => t) := by
    intro acc t H
    cases cs.a_fd with
    | FdFile k l o => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | FdStd => exact H
    | FdDir => exact H
  simp only [live_vars, live_vars_t]
  apply live_agree_expr
  apply hfd
  apply live_agree_fold
  · intro a acc t H
    exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
  apply live_agree_fold
  · intro a acc t H
    exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
  apply live_agree_fold
  · intro a acc t H
    exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
  apply live_agree_fold
  · intro a acc t H
    cases a with
    | KWord b w v => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | KZero b n => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | KBlob b n k => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | KWr b n => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | KFill b n c => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | KUnk b n => exact live_agree_expr _ _ _ (live_agree_expr _ _ _ H)
    | KImg lo hi => exact H
    | KAlign e m => exact H
    | KRange e lo hi => exact H
    | KDisj a1 n1 a2 n2 => exact H
  apply (live_agree_fold expr_vars expr_vars_t cs.a_ss.s_regs)
  · intro a acc t H; exact live_agree_expr _ _ _ H
  exact A0

/-! ## 4. Variable hygiene / syntactic equalities -/

/-- Every variable of `e` is below `b`. -/
def expr_vars_lt (b : Nat) : expr → Bool
  | .ELit _ => true
  | .EVar n => n < b
  | .EAlu _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EAluw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EMd _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EExt _ _ _ x => expr_vars_lt b x
  | .EBlob _ _ _ _ => true

/-- Every variable of the address's base is below `b`. -/
def saddr_vars_lt (b : Nat) (a : saddr) : Bool := expr_vars_lt b a.a_base

/-- Shapes mention only variables below `b` (`PMerge` re-tests it). -/
def shape_vars_lt (b : Nat) : shape → Bool
  | .SNil | .SExit _ | .SHole _ | .SNext => true
  | .SEmitP _ _ s' => shape_vars_lt b s'
  | .SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | .SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y

/-- Every variable of the knowledge entry is below `b`. -/
def kentry_vars_lt (b : Nat) (K : kentry) : Bool :=
  match K with
  | .KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | .KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | .KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | .KImg _ _ => true
  | .KAlign e _ => expr_vars_lt b e
  | .KRange e _ _ => expr_vars_lt b e
  | .KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | .KDisj a1 n1 a2 n2 =>
      saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | .KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | .KUnk a n => saddr_vars_lt b a && expr_vars_lt b n

/-- Every variable of the register file is below `b`. -/
def sr_vars_lt (b : Nat) : List expr → Bool
  | [] => true
  | e :: r => expr_vars_lt b e && sr_vars_lt b r

/-- Every variable of the knowledge list is below `b`. -/
def kn_vars_lt (b : Nat) : List kentry → Bool
  | [] => true
  | K :: r => kentry_vars_lt b K && kn_vars_lt b r

/-- Every variable of the pairs is below `b`. -/
def pairs_vars_lt (b : Nat) (l : List (expr × expr)) : Bool :=
  l.all (fun p => expr_vars_lt b p.1 && expr_vars_lt b p.2)

/-- Every variable of the ledger entries is below `b`. -/
def maps_vars_lt (b : Nat) (ms : List amap) : Bool :=
  ms.all (fun m => expr_vars_lt b m.am_base && expr_vars_lt b m.am_len)

/-- Every variable of the fd state is below `b`. -/
def fd_vars_lt (b : Nat) : afd → Bool
  | .FdStd => true
  | .FdFile _ l o => expr_vars_lt b l && expr_vars_lt b o
  | .FdDir => true

/-- The whole state mentions only variables below `nxt cs` (so `EVar (nxt cs)`
    is fresh), and the initial variables are below that too. -/
def fresh_ok (nx0 : Nat) (cs : acs) : Bool :=
  let v := nxt cs
  sr_vars_lt v cs.a_ss.s_regs && kn_vars_lt v (kn cs)
  && maps_vars_lt v cs.a_maps && pairs_vars_lt v cs.a_vis && pairs_vars_lt v cs.a_ghost
  && expr_vars_lt v cs.a_brk && fd_vars_lt v cs.a_fd && nx0 ≤ v

/-- Running one block in the executor's EXTENSION MODE (`AX2.sym_execTX`):
    loads from bytes known only to be mapped (`KUnk` / havoc'd
    ranges) yield FRESH variables without side conditions, and — if `K > 0` —
    every destination register whose expression exceeds `K` nodes is renamed
    to a fresh variable (register cap).  The entry state must be closed below
    its counter (`fresh_ok`), the exit log is carried into the knowledge and
    all side conditions must have been discharged. -/
def run_block_ref (segs : List Segment) (IT : itab) (nx0 : Nat) (K : Nat) (fuel : Nat)
    (stops : List Int) (cs : acs) : Option acs :=
  if fresh_ok nx0 cs then
    let ss := cs.a_ss
    let ss' := sym_execTX segs IT K fuel true stops
      (SS ss.s_pc ss.s_regs [] ss.s_know ss.s_next)
    match carry ss'.s_log ss'.s_know [] with
    | (kn', [], _) => some (with_ss cs (mk_ss ss'.s_pc ss'.s_regs kn' ss'.s_next))
    | _ => none
  else none

/-- PERF: the same through the executor's block-context functions
    (`AX2.mkbc`: the block's fact list, its sum-facts digest and range index
    computed ONCE and shared by the run and by every store of the carry;
    `AX2B.mk_kix`: the knowledge LOAD index, so that a load consults only
    the entries of its 4 KiB granule plus the always-candidates —
    `AX2B.sym_execTXBI`, `AX2B.carryK` (the vertical carry); `run_block_eq`:
    equal to `run_block_ref`).  The vertical carry is `carryK0` here:
    `AxSymExec3B.carryK0_eq` proves it equal to the reference `carry`. -/
def run_block (segs : List Segment) (IT : itab) (nx0 : Nat) (K : Nat) (fuel : Nat)
    (stops : List Int) (cs : acs) : Option acs :=
  if fresh_ok nx0 cs then
    let ss := cs.a_ss
    let bc := mkbc (facts_of ss.s_know)
    let kx := mk_kix ss.s_know       -- PERF: the knowledge load index of the block
    let ss' := sym_execTXBI segs bc kx IT K fuel true stops
      (SS ss.s_pc ss.s_regs [] ss.s_know ss.s_next)
    match carryK0 bc ss'.s_log ss'.s_know [] with
    | (kn', [], _) => some (with_ss cs (mk_ss ss'.s_pc ss'.s_regs kn' ss'.s_next))
    | _ => none
  else none

/-- `run_block = run_block_ref`. -/
theorem run_block_eq (segs : List Segment) (IT : itab) (nx0 : Nat) (K : Nat) (fuel : Nat)
    (stops : List Int) (cs : acs) :
    run_block segs IT nx0 K fuel stops cs = run_block_ref segs IT nx0 K fuel stops cs := by
  by_cases h : fresh_ok nx0 cs
  · simp only [run_block, run_block_ref, ite_eq_left h]
    rw [show sym_execTXBI segs (mkbc (facts_of cs.a_ss.s_know)) (mk_kix cs.a_ss.s_know)
              IT K fuel true stops
              (SS cs.a_ss.s_pc cs.a_ss.s_regs [] cs.a_ss.s_know cs.a_ss.s_next)
          = sym_execTX segs IT K fuel true stops
              (SS cs.a_ss.s_pc cs.a_ss.s_regs [] cs.a_ss.s_know cs.a_ss.s_next) from
        sym_execTXBI_eq segs _ IT K fuel true stops _ rfl]
    rw [sym_execTX_know segs IT K fuel true stops
          (SS cs.a_ss.s_pc cs.a_ss.s_regs [] cs.a_ss.s_know cs.a_ss.s_next)]
    rw [carryK0_eq]
  · simp only [run_block, run_block_ref, ite_eq_right h]

/-- The block run followed by the knowledge GC. -/
def run_block_gc (segs : List Segment) (IT : itab) (nx0 : Nat) (K : Nat) (fuel : Nat)
    (stops : List Int) (cs : acs) : Option acs :=
  match run_block segs IT nx0 K fuel stops cs with
  | some cs' => some (cs_gc nx0 cs')
  | none => none


/-! ## 5. Knowledge utilities -/

/-- Boolean equality of knowledge entries. -/
def kentry_eqb : kentry → kentry → Bool
  | .KWord a w v, .KWord a' w' v' => saddr_eqb a a' && (w == w') && expr_eqb v v'
  | .KZero a n, .KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | .KBlob a n k, .KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && (k == k')
  | .KImg lo hi, .KImg lo' hi' => (lo == lo') && (hi == hi')
  | .KAlign e m, .KAlign e' m' => expr_eqb e e' && (m == m')
  | .KRange e lo hi, .KRange e' lo' hi' => expr_eqb e e' && (lo == lo') && (hi == hi')
  | .KWr a n, .KWr a' n' => saddr_eqb a a' && expr_eqb n n'
  | .KDisj a1 n1 a2 n2, .KDisj a1' n1' a2' n2' =>
      saddr_eqb a1 a1' && expr_eqb n1 n1' && saddr_eqb a2 a2' && expr_eqb n2 n2'
  | .KFill a n c, .KFill a' n' c' => saddr_eqb a a' && expr_eqb n n' && (c == c')
  | .KUnk a n, .KUnk a' n' => saddr_eqb a a' && expr_eqb n n'
  | _, _ => false

/-- Boolean equality of ledger entries. -/
def amap_eqb (x y : amap) : Bool :=
  expr_eqb x.am_base y.am_base && expr_eqb x.am_len y.am_len && mkind_eqb x.am_kind y.am_kind

/-- Boolean equality of lists, given one for the elements. -/
def list_eqb {T : Type} (eqb : T → T → Bool) : List T → List T → Bool
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false

/-- Boolean equality of pairs of expressions. -/
def pair_eqb (x y : expr × expr) : Bool := expr_eqb x.1 y.1 && expr_eqb x.2 y.2

/-- Boolean equality of fd states. -/
def afd_eqb : afd → afd → Bool
  | .FdStd, .FdStd => true
  | .FdDir, .FdDir => true
  | .FdFile k l o, .FdFile k' l' o' => (k == k') && expr_eqb l l' && expr_eqb o o'
  | _, _ => false

/-- The footprint of `K` is provably apart from `ub+uk, +un` (lengths may be
    symbolic: `ranges_apart_x`). -/
def kentry_apart_b (allkn : List kentry) (ub : expr) (uk : Int) (un : expr) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, k⟩ w _ => (w ≤ 8) && ranges_apart_x allkn ub uk un b k (.ELit (w : Int))
  | .KZero ⟨b, k⟩ l => ranges_apart_x allkn ub uk un b k l
  | .KBlob ⟨b, k⟩ l _ => ranges_apart_x allkn ub uk un b k l
  | .KImg lo hi =>
      (0 ≤ lo) && (lo ≤ hi) && (hi - lo < two64) && ranges_apart_x allkn ub uk un (.ELit 0) lo (.ELit (hi - lo))
  | .KAlign _ _ => true
  | .KRange _ _ _ => true
  | .KDisj _ _ _ _ => true
  | .KWr ⟨b, k⟩ n => ranges_apart_x allkn ub uk un b k n
  | .KFill ⟨b, k⟩ l _ => ranges_apart_x allkn ub uk un b k l
  | .KUnk ⟨b, k⟩ l => ranges_apart_x allkn ub uk un b k l

/-- The same through the block context. -/
def kentry_apart_bB (bc : bctx) (ub : expr) (uk : Int) (un : expr) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, k⟩ w _ => (w ≤ 8) && ranges_apart_xB bc ub uk un b k (.ELit (w : Int))
  | .KZero ⟨b, k⟩ l => ranges_apart_xB bc ub uk un b k l
  | .KBlob ⟨b, k⟩ l _ => ranges_apart_xB bc ub uk un b k l
  | .KImg lo hi =>
      (0 ≤ lo) && (lo ≤ hi) && (hi - lo < two64) && ranges_apart_xB bc ub uk un (.ELit 0) lo (.ELit (hi - lo))
  | .KAlign _ _ => true
  | .KRange _ _ _ => true
  | .KDisj _ _ _ _ => true
  | .KWr ⟨b, k⟩ n => ranges_apart_xB bc ub uk un b k n
  | .KFill ⟨b, k⟩ l _ => ranges_apart_xB bc ub uk un b k l
  | .KUnk ⟨b, k⟩ l => ranges_apart_xB bc ub uk un b k l

/-- `kentry_apart_bB` at `mkbc fk` is `kentry_apart_b fk`. -/
theorem kentry_apart_bB_eqf (fk : List kentry) :
    kentry_apart_bB (mkbc fk) = kentry_apart_b fk := by
  funext ub uk un K
  cases K <;>
    simp only [kentry_apart_bB, kentry_apart_b, ranges_apart_xB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- P2: the same against a PREPARED range. -/
def kentry_apart_bp (allkn : List kentry) (sp : sprep) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, k⟩ w _ => (w ≤ 8) && ranges_apart_p allkn sp ub uk un b k (.ELit (w : Int))
  | .KZero ⟨b, k⟩ l => ranges_apart_p allkn sp ub uk un b k l
  | .KBlob ⟨b, k⟩ l _ => ranges_apart_p allkn sp ub uk un b k l
  | .KImg lo hi =>
      (0 ≤ lo) && (lo ≤ hi) && (hi - lo < two64) && ranges_apart_p allkn sp ub uk un (.ELit 0) lo (.ELit (hi - lo))
  | .KAlign _ _ => true
  | .KRange _ _ _ => true
  | .KDisj _ _ _ _ => true
  | .KWr ⟨b, k⟩ n => ranges_apart_p allkn sp ub uk un b k n
  | .KFill ⟨b, k⟩ l _ => ranges_apart_p allkn sp ub uk un b k l
  | .KUnk ⟨b, k⟩ l => ranges_apart_p allkn sp ub uk un b k l

/-- The prepared test through the block context. -/
def kentry_apart_bpB (bc : bctx) (sp : sprep) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, k⟩ w _ => (w ≤ 8) && ranges_apart_pB bc sp ub uk un b k (.ELit (w : Int))
  | .KZero ⟨b, k⟩ l => ranges_apart_pB bc sp ub uk un b k l
  | .KBlob ⟨b, k⟩ l _ => ranges_apart_pB bc sp ub uk un b k l
  | .KImg lo hi =>
      (0 ≤ lo) && (lo ≤ hi) && (hi - lo < two64) && ranges_apart_pB bc sp ub uk un (.ELit 0) lo (.ELit (hi - lo))
  | .KAlign _ _ => true
  | .KRange _ _ _ => true
  | .KDisj _ _ _ _ => true
  | .KWr ⟨b, k⟩ n => ranges_apart_pB bc sp ub uk un b k n
  | .KFill ⟨b, k⟩ l _ => ranges_apart_pB bc sp ub uk un b k l
  | .KUnk ⟨b, k⟩ l => ranges_apart_pB bc sp ub uk un b k l

/-- `kentry_apart_bpB` at `mkbc fk` is `kentry_apart_bp fk`. -/
theorem kentry_apart_bpB_eqf (fk : List kentry) :
    kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk := by
  funext sp ub uk un K
  cases K <;>
    simp only [kentry_apart_bpB, kentry_apart_bp, ranges_apart_pB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- Is the entry an image-overlay fact? -/
def kimg_b (K : kentry) : Bool :=
  match K with | .KImg _ _ => true | _ => false

/-- After the bytes of `ub+uk, +un` changed arbitrarily or were unmapped: keep
    only memory facts provably apart from the range (`KImg` facts survive: a
    write INSIDE the image hull keeps the overlay defined there ... no: `KImg`
    says the overlay is UNdefined, so `KImg` entries are CUT around the range by
    `kimg_cut` first where needed; `kn_unfill` keeps them,
    which is right for munmap / PROT_NONE (bytes become undefined) and for
    ranges known to be off the image hull). -/
def kn_unfill (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprep k ub uk un
  k.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K)

/-- The same through the block context. -/
def kn_unfillB (bc : bctx) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprepB bc ub uk un
  bc.bc_fk.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K)

/-- `kn_unfillB` at `mkbc fk` is `kn_unfill fk`. -/
theorem kn_unfillB_eqf (fk : List kentry) : kn_unfillB (mkbc fk) = kn_unfill fk := by
  funext ub uk un
  simp only [kn_unfillB, kn_unfill, mk_sprepB_eqf, bc_fk_mkbc, kentry_apart_bpB_eqf]
  try (with_unfolding_all exact rfl)

/-- `kn_unfill` through `mkbc`. -/
def kn_unfillM (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  kn_unfillB (mkbc k) ub uk un

/-- `kn_unfillM = kn_unfill`. -/
theorem kn_unfillM_eq : kn_unfillM = kn_unfill := by
  funext k ub uk un
  exact congrFun (congrFun (congrFun (kn_unfillB_eqf k) ub) uk) un

/-- Is the entry a writability fact? -/
def kwr_b (K : kentry) : Bool :=
  match K with | .KWr _ _ => true | _ => false

/-- Havoc of `ub+uk, +un` (a summarized routine wrote there): entries provably
    apart survive, a hit `KZero` is cut exactly around the range, `KWr` and
    pure facts survive. -/
def havoc1 (k : List kentry) (ub : expr) (uk : Int) (un : expr) (K : kentry) : List kentry :=
  if (kwr_b K || kentry_apart_b k ub uk un K) then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cut k ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cut c k ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cut k ub uk un kb kk len
    | _ => []

/-- The same through the block context. -/
def havoc1B (bc : bctx) (ub : expr) (uk : Int) (un : expr) (K : kentry) : List kentry :=
  if (kwr_b K || kentry_apart_bB bc ub uk un K) then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cutB bc ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cutB bc c ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cutB bc ub uk un kb kk len
    | _ => []

/-- `havoc1B` at `mkbc fk` is `havoc1 fk`. -/
theorem havoc1B_eqf (fk : List kentry) : havoc1B (mkbc fk) = havoc1 fk := by
  funext ub uk un K
  cases K <;>
    simp only [havoc1B, havoc1, kentry_apart_bB_eqf, kzero_cutB_eqf, kfill_cutB_eqf,
      kunk_cutB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- The prepared havoc. -/
def havoc1p (k : List kentry) (sp : sprep) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) : List kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K) then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cut k ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cut c k ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cut k ub uk un kb kk len
    | _ => []

/-- The prepared havoc through the block context. -/
def havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) : List kentry :=
  if (kwr_b K || kentry_apart_bpB bc sp ub uk un K) then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cutB bc ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cutB bc c ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cutB bc ub uk un kb kk len
    | _ => []

/-- `havoc1pB` at `mkbc fk` is `havoc1p fk`. -/
theorem havoc1pB_eqf (fk : List kentry) : havoc1pB (mkbc fk) = havoc1p fk := by
  funext sp ub uk un K
  cases K <;>
    simp only [havoc1pB, havoc1p, kentry_apart_bpB_eqf, kzero_cutB_eqf, kfill_cutB_eqf,
      kunk_cutB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- Havoc of a range over the whole knowledge. -/
def kn_havoc (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprep k ub uk un
  k.flatMap (havoc1p k sp ub uk un)

/-- The same through the block context. -/
def kn_havocB (bc : bctx) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprepB bc ub uk un
  bc.bc_fk.flatMap (havoc1pB bc sp ub uk un)

/-- `kn_havocB` at `mkbc fk` is `kn_havoc fk`. -/
theorem kn_havocB_eqf (fk : List kentry) : kn_havocB (mkbc fk) = kn_havoc fk := by
  funext ub uk un
  simp only [kn_havocB, kn_havoc, mk_sprepB_eqf, bc_fk_mkbc, havoc1pB_eqf]
  try (with_unfolding_all exact rfl)

/-- `kn_havoc` through `mkbc`. -/
def kn_havocM (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  kn_havocB (mkbc k) ub uk un

/-- `kn_havocM = kn_havoc`. -/
theorem kn_havocM_eq : kn_havocM = kn_havoc := by
  funext k ub uk un
  exact congrFun (congrFun (congrFun (kn_havocB_eqf k) ub) uk) un

/-- Cut-out of `ub+uk, +un` (the bytes there became inaccessible / changed
    their visibility: mmap arm G, PROT_NONE over a slice of a tracked rw
    entry): entries provably apart survive; `KZero`/`KFill`/`KWr` entries that
    are hit are CUT exactly around the range (the remaining pieces keep their
    meaning: the memory outside the range is unchanged); values
    (`KWord`/`KBlob`) that are hit go; pure facts and `KImg` survive (the
    caller clips `KImg` to the hull). -/
def kwr_cut (k : List kentry) (ub : expr) (uk : Int) (un : expr) (kb : expr) (kk : Int)
    (len : expr) : List kentry :=
  kcut .KWr k ub uk un kb kk len

/-- The same through the block context. -/
def kwr_cutB (bc : bctx) (ub : expr) (uk : Int) (un : expr) (kb : expr) (kk : Int)
    (len : expr) : List kentry :=
  kcutB bc .KWr ub uk un kb kk len

/-- `kwr_cutB` at `mkbc fk` is `kwr_cut fk`. -/
theorem kwr_cutB_eqf (fk : List kentry) : kwr_cutB (mkbc fk) = kwr_cut fk := by
  funext ub uk un kb kk len
  simp only [kwr_cutB, kwr_cut, kcutB_eqf]
  try (with_unfolding_all exact rfl)

/-- The cut-out of one entry. -/
def cutout1 (k : List kentry) (ub : expr) (uk : Int) (un : expr) (K : kentry) : List kentry :=
  if kentry_apart_b k ub uk un K then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cut k ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cut c k ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cut k ub uk un kb kk len
    | .KWr ⟨kb, kk⟩ len => kwr_cut k ub uk un kb kk len
    | _ => []

/-- The cut-out of one entry, through the block context. -/
def cutout1B (bc : bctx) (ub : expr) (uk : Int) (un : expr) (K : kentry) : List kentry :=
  if kentry_apart_bB bc ub uk un K then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cutB bc ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cutB bc c ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cutB bc ub uk un kb kk len
    | .KWr ⟨kb, kk⟩ len => kwr_cutB bc ub uk un kb kk len
    | _ => []

/-- `cutout1B` at `mkbc fk` is `cutout1 fk`. -/
theorem cutout1B_eqf (fk : List kentry) : cutout1B (mkbc fk) = cutout1 fk := by
  funext ub uk un K
  cases K <;>
    simp only [cutout1B, cutout1, kentry_apart_bB_eqf, kzero_cutB_eqf, kfill_cutB_eqf,
      kunk_cutB_eqf, kwr_cutB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- The prepared cut-out of one entry. -/
def cutout1p (k : List kentry) (sp : sprep) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) : List kentry :=
  if kentry_apart_bp k sp ub uk un K then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cut k ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cut c k ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cut k ub uk un kb kk len
    | .KWr ⟨kb, kk⟩ len => kwr_cut k ub uk un kb kk len
    | _ => []

/-- The prepared cut-out of one entry, through the block context. -/
def cutout1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) : List kentry :=
  if kentry_apart_bpB bc sp ub uk un K then [K]
  else
    match K with
    | .KZero ⟨kb, kk⟩ len => kzero_cutB bc ub uk un kb kk len
    | .KFill ⟨kb, kk⟩ len c => kfill_cutB bc c ub uk un kb kk len
    | .KUnk ⟨kb, kk⟩ len => kunk_cutB bc ub uk un kb kk len
    | .KWr ⟨kb, kk⟩ len => kwr_cutB bc ub uk un kb kk len
    | _ => []

/-- `cutout1pB` at `mkbc fk` is `cutout1p fk`. -/
theorem cutout1pB_eqf (fk : List kentry) : cutout1pB (mkbc fk) = cutout1p fk := by
  funext sp ub uk un K
  cases K <;>
    simp only [cutout1pB, cutout1p, kentry_apart_bpB_eqf, kzero_cutB_eqf, kfill_cutB_eqf,
      kunk_cutB_eqf, kwr_cutB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- Cut-out of a range over the whole knowledge. -/
def kn_cutout (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprep k ub uk un
  k.flatMap (cutout1p k sp ub uk un)

/-- The same through the block context. -/
def kn_cutoutB (bc : bctx) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprepB bc ub uk un
  bc.bc_fk.flatMap (cutout1pB bc sp ub uk un)

/-- `kn_cutoutB` at `mkbc fk` is `kn_cutout fk`. -/
theorem kn_cutoutB_eqf (fk : List kentry) : kn_cutoutB (mkbc fk) = kn_cutout fk := by
  funext ub uk un
  simp only [kn_cutoutB, kn_cutout, mk_sprepB_eqf, bc_fk_mkbc, cutout1pB_eqf]
  try (with_unfolding_all exact rfl)

/-- `kn_cutout` through `mkbc`. -/
def kn_cutoutM (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  kn_cutoutB (mkbc k) ub uk un

/-- `kn_cutoutM = kn_cutout`. -/
theorem kn_cutoutM_eq : kn_cutoutM = kn_cutout := by
  funext k ub uk un
  exact congrFun (congrFun (congrFun (kn_cutoutB_eqf k) ub) uk) un

/-- `PGcKeep ws`: knowledge GC against KEEP WINDOWS: a window is (lo, len); a
    memory-CONTENT fact (KWord/KZero/KBlob/KFill) whose base (after `split_lit`)
    is the base of SOME window ("in scope") but whose offset interval
    `[o, o+n)` (n: its upper bound, or unbounded) intersects NO window of that
    base is dropped; everything else is kept (pure weakening). -/
def kn_keep (k : List kentry) (ws : List (expr × expr)) : List kentry :=
  let wss := ws.map (fun w => (split_lit w.1, xlo k w.2))
  let test (b : expr) (o : Int) (n : Option Int) : Bool :=
    let mine := wss.filter (fun w => expr_eqb w.1.1 b)
    match mine with
    | [] => true
    | _ =>
      mine.any (fun w =>
        let wk := w.1.2
        match w.2 with
        | some wl => (0 < wl) && (wk < (match n with | some n => o + n | none => wk + 1))
                     && (o < wk + wl)
        | none => true)
  k.filter (fun K =>
    match K with
    | .KWord ⟨b, o⟩ w _ => test b o (some (w : Int))
    | .KZero ⟨b, o⟩ n => test b o (xhi k n)
    | .KBlob ⟨b, o⟩ n _ => test b o (xhi k n)
    | .KFill ⟨b, o⟩ n _ => test b o (xhi k n)
    | .KUnk ⟨b, o⟩ n => test b o (xhi k n)
    | _ => true)

/-- Cut the absolute range `[a, a+n)` out of every `KImg` entry (a weakening). -/
def kimg_cut1 (a n : Int) (K : kentry) : List kentry :=
  match K with
  | .KImg lo hi =>
      if (hi ≤ a || a + n ≤ lo) then [K]
      else (if lo < a then [.KImg lo a] else [])
           ++ (if a + n < hi then [.KImg (a + n) hi] else [])
  | _ => [K]

/-- `kimg_cut1` over a knowledge list. -/
def kimg_cut (k : List kentry) (a n : Int) : List kentry := k.flatMap (kimg_cut1 a n)

/-- Keep `KImg` facts only inside the image hull (where visibility never
    changes); applied by every node that changes the hidden set. -/
def kimg_clip (A : atable) (k : List kentry) : List kentry :=
  k.filter (fun K =>
    match K with
    | .KImg lo hi => A.img_lo ≤ lo && lo ≤ hi && hi ≤ A.img_hi
    | _ => true)

/-- n-byte literal read from the knowledge (`n <= 8`). -/
def kreadZ (segs : List Segment) (k : List kentry) (b : expr) (off : Int) (n : Nat) : Option Int :=
  match know_lookup segs k b off n false [] [] with
  | .LHit (.ELit z) [] _ => some (z % two64)
  | _ => none

/-- The same through the block context. -/
def kreadZB (segs : List Segment) (bc : bctx) (b : expr) (off : Int) (n : Nat) : Option Int :=
  match know_lookupB segs bc b off n false [] [] with
  | .LHit (.ELit z) [] _ => some (z % two64)
  | _ => none

/-- `kreadZB` at `mkbc fk` is `kreadZ fk`. -/
theorem kreadZB_eqf (segs : List Segment) (fk : List kentry) :
    kreadZB segs (mkbc fk) = kreadZ segs fk := by
  funext b off n
  simp only [kreadZB, kreadZ, know_lookupB_eqf]

/-- 8-byte symbolic read. -/
def kread8e (segs : List Segment) (k : List kentry) (b : expr) (off : Int) : Option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | .LHit v [] _ => some v
  | _ => none

/-- The same through the block context. -/
def kread8eB (segs : List Segment) (bc : bctx) (b : expr) (off : Int) : Option expr :=
  match know_lookupB segs bc b off 8 false [] [] with
  | .LHit v [] _ => some v
  | _ => none

/-- `kread8eB` at `mkbc fk` is `kread8e fk`. -/
theorem kread8eB_eqf (segs : List Segment) (fk : List kentry) :
    kread8eB segs (mkbc fk) = kread8e segs fk := by
  funext b off
  simp only [kread8eB, kread8e, know_lookupB_eqf]

/-- `b+off, +n` writable by a `KWr` entry (`n` literal). -/
def kwritable (allkn : List kentry) : List kentry → expr → Int → Int → Bool
  | [], _, _, _ => false
  | .KWr ⟨wb, wk⟩ wn :: rest, b, off, n =>
      if (if (expr_eqb b wb && wk ≤ off)
          then match xlo allkn wn with
               | some wl => off + n ≤ wk + wl
               | none => false
          else false)
      then true
      else if (0 ≤ n && n < two64 && xinside allkn b off (.ELit n) wb wk wn) then true
      else kwritable allkn rest b off n
  | _ :: rest, b, off, n => kwritable allkn rest b off n

/-- The same through the block context. -/
def kwritableB (bc : bctx) : List kentry → expr → Int → Int → Bool
  | [], _, _, _ => false
  | .KWr ⟨wb, wk⟩ wn :: rest, b, off, n =>
      if (if (expr_eqb b wb && wk ≤ off)
          then match xloB bc wn with
               | some wl => off + n ≤ wk + wl
               | none => false
          else false)
      then true
      else if (0 ≤ n && n < two64 && xinsideB bc b off (.ELit n) wb wk wn) then true
      else kwritableB bc rest b off n
  | _ :: rest, b, off, n => kwritableB bc rest b off n

/-- `kwritableB` at `mkbc fk` is `kwritable fk`. -/
theorem kwritableB_eqf (fk : List kentry) : kwritableB (mkbc fk) = kwritable fk := by
  funext k b off n
  induction k generalizing b off n with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KWr a wn =>
          obtain ⟨wb, wk⟩ := a
          simp only [kwritableB, kwritable, ih, xloB_eqf, xinsideB_eqf]
          try (with_unfolding_all exact rfl)
      | _ =>
          simp only [kwritableB, kwritable, ih]
          try (with_unfolding_all exact rfl)

/-- `b+off, +n` writable by a `KWr` entry (`n` symbolic). -/
def kwritable_x (allkn : List kentry) : List kentry → expr → Int → expr → Bool
  | [], _, _, _ => false
  | .KWr ⟨wb, wk⟩ wn :: rest, b, off, n =>
      if (if (expr_eqb b wb && wk ≤ off)
          then match xhi allkn n, xlo allkn wn with
               | some nh, some wl => off + nh ≤ wk + wl
               | _, _ => false
          else false)
      then true
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest, b, off, n => kwritable_x allkn rest b off n

/-- The same through the block context. -/
def kwritable_xB (bc : bctx) : List kentry → expr → Int → expr → Bool
  | [], _, _, _ => false
  | .KWr ⟨wb, wk⟩ wn :: rest, b, off, n =>
      if (if (expr_eqb b wb && wk ≤ off)
          then match xhiB bc n, xloB bc wn with
               | some nh, some wl => off + nh ≤ wk + wl
               | _, _ => false
          else false)
      then true
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest, b, off, n => kwritable_xB bc rest b off n

/-- `kwritable_xB` at `mkbc fk` is `kwritable_x fk`. -/
theorem kwritable_xB_eqf (fk : List kentry) : kwritable_xB (mkbc fk) = kwritable_x fk := by
  funext k b off n
  induction k generalizing b off n with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KWr a wn =>
          obtain ⟨wb, wk⟩ := a
          simp only [kwritable_xB, kwritable_x, ih, xloB_eqf, xhiB_eqf, xinsideB_eqf]
          try (with_unfolding_all exact rfl)
      | _ =>
          simp only [kwritable_xB, kwritable_x, ih]
          try (with_unfolding_all exact rfl)

/-- `b+off, +n` readable as ZERO bytes by one `KZero` entry (`n` symbolic). -/
def kzero_x (allkn : List kentry) : List kentry → expr → Int → expr → Bool
  | [], _, _, _ => false
  | .KZero ⟨zb, zk⟩ zn :: rest, b, off, n =>
      if (if (expr_eqb b zb && zk ≤ off)
          then match xhi allkn n, xlo allkn zn with
               | some nh, some zl => off + nh ≤ zk + zl
               | _, _ => false
          else false)
      then true
      else if xinside allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest, b, off, n => kzero_x allkn rest b off n

/-- The same through the block context. -/
def kzero_xB (bc : bctx) : List kentry → expr → Int → expr → Bool
  | [], _, _, _ => false
  | .KZero ⟨zb, zk⟩ zn :: rest, b, off, n =>
      if (if (expr_eqb b zb && zk ≤ off)
          then match xhiB bc n, xloB bc zn with
               | some nh, some zl => off + nh ≤ zk + zl
               | _, _ => false
          else false)
      then true
      else if xinsideB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest, b, off, n => kzero_xB bc rest b off n

/-- `kzero_xB` at `mkbc fk` is `kzero_x fk`. -/
theorem kzero_xB_eqf (fk : List kentry) : kzero_xB (mkbc fk) = kzero_x fk := by
  funext k b off n
  induction k generalizing b off n with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KZero a zn =>
          obtain ⟨zb, zk⟩ := a
          simp only [kzero_xB, kzero_x, ih, xloB_eqf, xhiB_eqf, xinsideB_eqf]
          try (with_unfolding_all exact rfl)
      | _ =>
          simp only [kzero_xB, kzero_x, ih]
          try (with_unfolding_all exact rfl)

/-- `b+off, +n` readable as bytes all equal to `c` by one `KFill` entry (`n`
    symbolic). -/
def kfill_x (allkn : List kentry) : List kentry → expr → Int → expr → Int → Bool
  | [], _, _, _, _ => false
  | .KFill ⟨zb, zk⟩ zn c' :: rest, b, off, n, c =>
      if (if (c' % 256 == c % 256 && expr_eqb b zb && zk ≤ off)
          then match xhi allkn n, xlo allkn zn with
               | some nh, some zl => off + nh ≤ zk + zl
               | _, _ => false
          else false)
      then true
      else if (c' % 256 == c % 256 && xinside allkn b off n zb zk zn) then true
      else kfill_x allkn rest b off n c
  | _ :: rest, b, off, n, c => kfill_x allkn rest b off n c

/-- The same through the block context. -/
def kfill_xB (bc : bctx) : List kentry → expr → Int → expr → Int → Bool
  | [], _, _, _, _ => false
  | .KFill ⟨zb, zk⟩ zn c' :: rest, b, off, n, c =>
      if (if (c' % 256 == c % 256 && expr_eqb b zb && zk ≤ off)
          then match xhiB bc n, xloB bc zn with
               | some nh, some zl => off + nh ≤ zk + zl
               | _, _ => false
          else false)
      then true
      else if (c' % 256 == c % 256 && xinsideB bc b off n zb zk zn) then true
      else kfill_xB bc rest b off n c
  | _ :: rest, b, off, n, c => kfill_xB bc rest b off n c

/-- `kfill_xB` at `mkbc fk` is `kfill_x fk`. -/
theorem kfill_xB_eqf (fk : List kentry) : kfill_xB (mkbc fk) = kfill_x fk := by
  funext k b off n c
  induction k generalizing b off n c with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KFill a zn c' =>
          obtain ⟨zb, zk⟩ := a
          simp only [kfill_xB, kfill_x, ih, xloB_eqf, xhiB_eqf, xinsideB_eqf]
          try (with_unfolding_all exact rfl)
      | _ =>
          simp only [kfill_xB, kfill_x, ih]
          try (with_unfolding_all exact rfl)

/-- apart from the image hull (so writable => overlay-defined). -/
def off_image_x (A : atable) (k : List kentry) (b : expr) (off : Int) (n : expr) : Bool :=
  ranges_apart_x k b off n (.ELit 0) A.img_lo (.ELit (A.img_hi - A.img_lo))

/-- The same through the block context. -/
def off_image_xB (A : atable) (bc : bctx) (b : expr) (off : Int) (n : expr) : Bool :=
  ranges_apart_xB bc b off n (.ELit 0) A.img_lo (.ELit (A.img_hi - A.img_lo))

/-- `off_image_xB` at `mkbc fk` is `off_image_x fk`. -/
theorem off_image_xB_eqf (A : atable) (fk : List kentry) :
    off_image_xB A (mkbc fk) = off_image_x A fk := by
  funext b off n
  simp only [off_image_xB, off_image_x, ranges_apart_xB_eqf]
  try (with_unfolding_all exact rfl)

/-- `b+off, +n` lies flat: `0 <= lo`, `hi + n <= 2^64`, and `n > 0`. -/
def flat_x (k : List kentry) (b : expr) (off : Int) (n : expr) : Bool :=
  match base_range k b, xlo k n, xhi k n with
  | some (lo, hi), some nl, some nh => (0 ≤ lo + off && hi + off + nh ≤ two64 && 0 < nl)
  | _, _, _ => false

/-- The same through the block context. -/
def flat_xB (bc : bctx) (b : expr) (off : Int) (n : expr) : Bool :=
  match base_rangeB bc b, xloB bc n, xhiB bc n with
  | some (lo, hi), some nl, some nh => (0 ≤ lo + off && hi + off + nh ≤ two64 && 0 < nl)
  | _, _, _ => false

/-- `flat_xB` at `mkbc fk` is `flat_x fk`. -/
theorem flat_xB_eqf (fk : List kentry) : flat_xB (mkbc fk) = flat_x fk := by
  funext b off n
  simp only [flat_xB, flat_x, base_rangeB_eqf, xloB_eqf, xhiB_eqf]
  try (with_unfolding_all exact rfl)

/-- Upper bound of an expression's value. -/
def ehi (k : List kentry) (e : expr) : Option Int := xhi k e

/-- Lower bound of an expression's value. -/
def elo (k : List kentry) (e : expr) : Option Int := xlo k e

/-- Two expressions provably denote the same value: syntactically, or as
    linear forms. -/
def len_eqb (k : List kentry) (n m : expr) : Bool :=
  expr_eqb n m
  || (lin_ge0 k [(n, (0 : Int))] [(m, (0 : Int))] && lin_ge0 k [(m, (0 : Int))] [(n, (0 : Int))])

/-- The same through the block context. -/
def len_eqbB (bc : bctx) (n m : expr) : Bool :=
  expr_eqb n m
  || (lin_ge0B bc [(n, (0 : Int))] [(m, (0 : Int))]
      && lin_ge0B bc [(m, (0 : Int))] [(n, (0 : Int))])

/-- `len_eqbB` at `mkbc fk` is `len_eqb fk`. -/
theorem len_eqbB_eqf (fk : List kentry) : len_eqbB (mkbc fk) = len_eqb fk := by
  funext n m
  simp only [len_eqbB, len_eqb, lin_ge0B_eqf]
  try (with_unfolding_all exact rfl)

/-- the literal difference `e - f` if the linear normal form of it is closed. -/
def lit_diff (e f : expr) : Option Int :=
  match esub e f with
  | .ELit z => some (z % two64)
  | _ => none

/-- provable page alignment of an expression. -/
def page_aligned (k : List kentry) (e : expr) : Bool :=
  match e with
  | .ELit z => (z % 4096 == 0)
  | _ => 12 ≤ ealign k e

/-- The same through the block context. -/
def page_alignedB (bc : bctx) (e : expr) : Bool :=
  match e with
  | .ELit z => (z % 4096 == 0)
  | _ => 12 ≤ ealignB bc e

/-- `page_alignedB` at `mkbc fk` is `page_aligned fk`. -/
theorem page_alignedB_eqf (fk : List kentry) : page_alignedB (mkbc fk) = page_aligned fk := by
  funext e
  cases e <;> simp only [page_alignedB, page_aligned, ealignB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- Cheap syntactic contradiction in the knowledge. -/
def kn_contra (k : List kentry) : Bool :=
  k.any (fun K =>
    match K with
    | .KRange e lo hi =>
        if hi < lo then true
        else
          match e with
          | .EVar _ => false
          | _ =>
            let l := lin_of e
            match l.2 with
            | _ :: _ :: _ =>
                match lin_range (erange k) l.1 l.2 with
                | some (a, b) => (0 ≤ a && b < two64 && (b < lo || hi < a))
                | none => false
            | _ => false
    | _ => false)

/-! ## 6. Registers after a call -/

/-- RISC-V caller-saved registers (ra, t0-t6, a0-a7); after a summarized call
    they hold unknown values = fresh variables. -/
def caller_saved : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- Re-spell the registers `ixs` as the fresh variables `nx, nx+1, ...`. -/
def sr_fresh (sr : List expr) : List Nat → Nat → List expr
  | [], _ => sr
  | i :: t, nx => sr_fresh (sr_upd sr i (.EVar nx)) t (nx + 1)

/-- The number of caller-saved registers. -/
def NCS : Nat := 16

/-- The return address register as a literal (even, in range). -/
def ret_lit (cs : acs) : Option Int :=
  match reg cs 1 with
  | .ELit r => if (r % 2 == 0 && r < two64 && 0 ≤ r) then some r else none
  | _ => none

/-- State after a summarized routine returned to `ret`: caller-saved
    registers fresh (16 new variables), then a0 := `rv` if given, knowledge
    := `k'`. -/
def after_call (nx0 : Nat) (cs : acs) (ret : Int) (rv : Option expr)
    (k' : List kentry) : Option acs :=
  let ss := cs.a_ss
  let nx := ss.s_next
  let sr1 := sr_fresh ss.s_regs caller_saved nx
  let sr2 := match rv with | some e => sr_upd sr1 10 e | none => sr1
  if (fresh_ok nx0 cs && kn_vars_lt nx k'
      && match rv with | some e => expr_vars_lt nx e | none => true)
  then some (with_ss cs (mk_ss ret sr2 k' (nx + NCS)))
  else none

/-- the same with `extra` more fresh variables `nx+NCS ..)` that `k'` may mention
    (their meaning is fixed by the node's soundness proof: e.g. the words of a
    havoc'd copy destination). -/
def after_call2 (nx0 : Nat) (cs : acs) (ret : Int) (rv : Option expr) (k' : List kentry)
    (extra : Nat) : Option acs :=
  let ss := cs.a_ss
  let nx := ss.s_next
  let sr1 := sr_fresh ss.s_regs caller_saved nx
  let sr2 := match rv with | some e => sr_upd sr1 10 e | none => sr1
  if (fresh_ok nx0 cs && kn_vars_lt (nx + NCS + extra) k'
      && match rv with | some e => expr_vars_lt nx e | none => true)
  then some (with_ss cs (mk_ss ret sr2 k' (nx + NCS + extra)))
  else none

/-! ## 8. Node checkers -/

/-- Page rounding up. -/
def page_up (len : Int) : Int := ((len + 4095) / 4096) * 4096

/-- Is the instruction at the pc an ecall? -/
def is_ecall_at (segs : List Segment) (cs : acs) : Bool :=
  (0 ≤ pc cs && pc cs + 4 < two64 &&
   match fetch_word segs (Z_to_bv 64 (pc cs)) with
   | some w => is_ecall w
   | none => false)

/-! ### 8.1 split / fact / forget / fresh -/

/-- tighter of the interval domain and the sum-fact bounds. -/
def xlo1 (k : List kentry) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
    match erange k e, lin_brange k e with
    | some (lo, _), some (lo', _) => some (max lo lo')
    | some (lo, _), none => some lo
    | none, some (lo', _) => some lo'
    | none, none => match lin_srange k e with | some (lo, _) => some lo | none => none

/-- The same through the block context. -/
def xlo1B (bc : bctx) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
    match erangeB bc e, lin_brangeB bc e with
    | some (lo, _), some (lo', _) => some (max lo lo')
    | some (lo, _), none => some lo
    | none, some (lo', _) => some lo'
    | none, none => match lin_srangeB bc e with | some (lo, _) => some lo | none => none

/-- `xlo1B` at `mkbc fk` is `xlo1 fk`. -/
theorem xlo1B_eqf (fk : List kentry) : xlo1B (mkbc fk) = xlo1 fk := by
  funext e
  cases e <;> simp only [xlo1B, xlo1, erangeB_eqf, lin_brangeB_eqf, lin_srangeB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- tighter of the interval domain and the sum-fact upper bounds. -/
def xhi1 (k : List kentry) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
    match erange k e, lin_brange k e with
    | some (_, hi), some (_, hi') => some (min hi hi')
    | some (_, hi), none => some hi
    | none, some (_, hi') => some hi'
    | none, none => match lin_srange k e with | some (_, hi) => some hi | none => none

/-- The same through the block context. -/
def xhi1B (bc : bctx) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
    match erangeB bc e, lin_brangeB bc e with
    | some (_, hi), some (_, hi') => some (min hi hi')
    | some (_, hi), none => some hi
    | none, some (_, hi') => some hi'
    | none, none => match lin_srangeB bc e with | some (_, hi) => some hi | none => none

/-- `xhi1B` at `mkbc fk` is `xhi1 fk`. -/
theorem xhi1B_eqf (fk : List kentry) : xhi1B (mkbc fk) = xhi1 fk := by
  funext e
  cases e <;> simp only [xhi1B, xhi1, erangeB_eqf, lin_brangeB_eqf, lin_srangeB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- Align-down atoms inside a sum: `deand e = (e', s)` replaces every
    `x AND -2^j` reachable through `ALU_ADD` nodes by `x`; the value of `e`
    is then `u e' - rho` (mod 2^64) for some `0 <= rho <= s`.  So when
    `e'` is bounded by `lo', hi'` with `s <= lo'`, `e` lies in
    `lo' - s, hi'` — the sum facts about the UNROUNDED form `e'` (e.g. a
    shadow address OFF + a/8 before RoundDown to 8) bound the rounded one. -/
def deand (e : expr) : expr × Int :=
  match e with
  | .EAlu .AND x (.ELit m) =>
      let m' := m % two64
      let j := zlog2 (two64 - m')
      if (two64 - m' == zpow 2 j && j ≤ 48)
      then
        let (x', s) := deand x
        (x', s + (zpow 2 j - 1))
      else (e, 0)
  | .EAlu .ADD a b =>
      let (a', s1) := deand a
      let (b', s2) := deand b
      (.EAlu .ADD a' b', s1 + s2)
  | _ => (e, 0)

/-- The tightened interval with the align-down refinement. -/
def xb2 (k : List kentry) (e : expr) : Option (Int × Int) :=
  let plain := match xlo1 k e, xhi1 k e with
    | some lo, some hi => some (lo, hi)
    | _, _ => none
  let (e', s) := deand e
  if s == 0 then plain
  else
    match xlo1 k e', xhi1 k e' with
    | some lo', some hi' =>
        if s ≤ lo' then
          match plain with
          | some (lo, hi) => some (max lo (lo' - s), min hi hi')
          | none => some (lo' - s, hi')
        else plain
    | _, _ => plain

/-- The same through the block context. -/
def xb2B (bc : bctx) (e : expr) : Option (Int × Int) :=
  let plain := match xlo1B bc e, xhi1B bc e with
    | some lo, some hi => some (lo, hi)
    | _, _ => none
  let (e', s) := deand e
  if s == 0 then plain
  else
    match xlo1B bc e', xhi1B bc e' with
    | some lo', some hi' =>
        if s ≤ lo' then
          match plain with
          | some (lo, hi) => some (max lo (lo' - s), min hi hi')
          | none => some (lo' - s, hi')
        else plain
    | _, _ => plain

/-- `xb2B` at `mkbc fk` is `xb2 fk`. -/
theorem xb2B_eqf (fk : List kentry) : xb2B (mkbc fk) = xb2 fk := by
  funext e
  simp only [xb2B, xb2, xlo1B_eqf, xhi1B_eqf]
  try (with_unfolding_all exact rfl)

/-- The tightened lower bound. -/
def xlo2 (k : List kentry) (e : expr) : Option Int :=
  match xb2 k e with | some (lo, _) => some lo | none => none

/-- The same through the block context. -/
def xlo2B (bc : bctx) (e : expr) : Option Int :=
  match xb2B bc e with | some (lo, _) => some lo | none => none

/-- `xlo2B` at `mkbc fk` is `xlo2 fk`. -/
theorem xlo2B_eqf (fk : List kentry) : xlo2B (mkbc fk) = xlo2 fk := by
  funext e
  simp only [xlo2B, xlo2, xb2B_eqf]
  try (with_unfolding_all exact rfl)

/-- The tightened upper bound. -/
def xhi2 (k : List kentry) (e : expr) : Option Int :=
  match xb2 k e with | some (_, hi) => some hi | none => none

/-- The same through the block context. -/
def xhi2B (bc : bctx) (e : expr) : Option Int :=
  match xb2B bc e with | some (_, hi) => some hi | none => none

/-- `xhi2B` at `mkbc fk` is `xhi2 fk`. -/
theorem xhi2B_eqf (fk : List kentry) : xhi2B (mkbc fk) = xhi2 fk := by
  funext e
  simp only [xhi2B, xhi2, xb2B_eqf]
  try (with_unfolding_all exact rfl)

/-- `PFact K`: facts the checker can verify. -/
def fact_ok (k : List kentry) (K : kentry) : Bool :=
  match K with
  | .KRange e lo hi =>
      match xlo2 k e, xhi2 k e with
      | some l, some h => lo ≤ l && h ≤ hi
      | _, _ => false
  | .KAlign e m => 0 < m && (m == zpow 2 (zlog2 m)) && (zlog2 m ≤ ealign k e)
  | .KDisj ⟨b1, k1⟩ n1 ⟨b2, k2⟩ n2 => ranges_apart_x k b1 k1 n1 b2 k2 n2
  | _ => false

/-- `PJoin b off n`: the n (<= 8) bytes at `b+off` each read as a literal
    through the knowledge; add the joined little-endian word as ONE fact. -/
def kread_bytes (segs : List Segment) (fuel : Nat) (k : List kentry) (b : expr) (off : Int) :
    Option (List Int) :=
  match fuel with
  | 0 => some []
  | f + 1 =>
      match kreadZ segs k b off 1, kread_bytes segs f k b (off + 1) with
      | some z, some rest => some (z :: rest)
      | _, _ => none

/-- The same through the block context. -/
def kread_bytesB (segs : List Segment) (bc : bctx) (fuel : Nat) (b : expr) (off : Int) :
    Option (List Int) :=
  match fuel with
  | 0 => some []
  | f + 1 =>
      match kreadZB segs bc b off 1, kread_bytesB segs bc f b (off + 1) with
      | some z, some rest => some (z :: rest)
      | _, _ => none

/-- `kread_bytesB` at `mkbc fk`, at fixed fuel. -/
theorem kread_bytesB_eqf' (segs : List Segment) (fk : List kentry) (fuel : Nat) :
    kread_bytesB segs (mkbc fk) fuel = kread_bytes segs fuel fk := by
  funext b off
  induction fuel generalizing b off with
  | zero => rfl
  | succ f ih =>
      simp only [kread_bytesB, kread_bytes, kreadZB_eqf, ih]
      try (with_unfolding_all exact rfl)

/-- `kread_bytesB` at `mkbc fk`. -/
theorem kread_bytesB_eqf (segs : List Segment) (fk : List kentry) :
    kread_bytesB segs (mkbc fk) = fun fuel => kread_bytes segs fuel fk := by
  funext fuel
  exact kread_bytesB_eqf' segs fk fuel

/-- `PJoin`: read the bytes and add the joined word as one fact. -/
def node_join (segs : List Segment) (cs : acs) (b : expr) (off : Int) (n : Nat) : Option acs :=
  if (1 ≤ n && n ≤ 8 && flat_x (kn cs) b off (.ELit (n : Int))) then
    match kread_bytes segs n (kn cs) b off with
    | some bs => some (add_kn cs [.KWord (SA b off) n (.ELit (zbytes_le_to_Z bs))])
    | none => none
  else none

/-- Drop the knowledge entries at the listed indices. -/
def drop_ixs (ixs : List Nat) (i : Nat) (k : List kentry) : List kentry :=
  match k with
  | [] => []
  | K :: r =>
      if ixs.any (fun x => i == x) then drop_ixs ixs (i + 1) r
      else K :: drop_ixs ixs (i + 1) r

/-- `PFresh r logc base`: with e := reg r - base (base = ELit 0 when absent),
    provably a multiple of c = 2^logc with bounds `lo, hi`: reg r becomes
    base + c * v (v fresh) with KRange v ceil(lo/c) (hi/c), the exact
    identity KRange (e - c*v) 0 0, and — when e contains align-down atoms,
    `deand e = (e', s)`, s > 0, e' bounded from below by s — the residue
    fact KRange (e' - c*v) 0 s (e.g. e = AND a (-8): KRange (a - 8v) 0 7). -/
def residue_fact (k : List kentry) (e ne : expr) : List kentry :=
  let (e', s) := deand e
  if 0 < s then
    match xlo1 k e', xhi1 k e' with
    | some lo', some _ => if s ≤ lo' then [.KRange (esub e' ne) 0 s] else []
    | _, _ => []
  else []

/-- `PFresh`. -/
def node_fresh (nx0 : Nat) (cs : acs) (r : Nat) (logc : Int) (base : Option expr) : Option acs :=
  let k := kn cs
  let c := zpow 2 logc
  let b := match base with | some b => b | none => .ELit 0
  let e := esub (reg cs r) b
  if (0 < r && r < 32 && 0 ≤ logc && logc ≤ 40 && logc ≤ ealign k e
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok nx0 cs) then
    match xlo2 k e, xhi2 k e with
    | some lo, some hi =>
        let v := nxt cs
        let ne := escale c (.EVar v)
        let kres := residue_fact k e ne
        let kf := .KRange (.EVar v) ((lo + c - 1) / c) (hi / c)
                  :: .KRange (esub e ne) 0 0 :: kres
        some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => none
  else none

/-- `PDropRange b n`: forget what the memory facts say about `b, b+n` (pure
    weakening: value facts not provably apart are dropped, KZero facts cut). -/
def node_droprange (cs : acs) (b n : expr) : acs :=
  let (bb, bk) := split_lit b
  set_kn cs (kn_havoc (kn cs) bb bk n)

/-- `PBump m`: nxt := m (m >= nxt). -/
def node_bump (cs : acs) (m : Nat) : Option acs :=
  if nxt cs ≤ m then some (bump cs (m - nxt cs)) else none

/-- `PHavoc rs`: registers rs (each in 1..31) := fresh variables nxt, nxt+1, ...
    in list order. -/
def node_havoc (nx0 : Nat) (cs : acs) (rs : List Nat) : Option acs :=
  if (fresh_ok nx0 cs && rs.all (fun r => 0 < r && r < 32)) then
    let ss := cs.a_ss
    some (with_ss cs (mk_ss ss.s_pc (sr_fresh ss.s_regs rs ss.s_next) ss.s_know
      (ss.s_next + rs.length)))
  else none

/-- `PHavocBig K` (the hash rounds square expression sizes): every
    register (x1..x31) and every `KWord` value whose expression has more than
    `K` nodes becomes a fresh variable (pure weakening + valuation extension). -/
def esize : expr → Nat
  | .EAlu _ a b => 1 + (esize a + esize b)
  | .EAluw _ a b => 1 + (esize a + esize b)
  | .EMd _ a b => 1 + (esize a + esize b)
  | .EMdw _ a b => 1 + (esize a + esize b)
  | .EExt _ _ _ a => 1 + esize a
  | _ => 1

/-- Is the expression bigger than `K` nodes? -/
def bigb (K : Nat) (e : expr) : Bool := K < esize e

/-- Re-spell the big `KWord` values as fresh variables. -/
def kn_bigsubst (K : Nat) (k : List kentry) (nx : Nat) : List kentry × Nat :=
  match k with
  | [] => ([], 0)
  | .KWord a w v :: r =>
      if bigb K v then
        let (r', c) := kn_bigsubst K r (nx + 1)
        (.KWord a w (.EVar nx) :: r', c + 1)
      else
        let (r', c) := kn_bigsubst K r nx
        (.KWord a w v :: r', c)
  | x :: r =>
      let (r', c) := kn_bigsubst K r nx
      (x :: r', c)

/-- `PHavocBig`. -/
def node_havocbig (nx0 : Nat) (cs : acs) (K : Nat) : Option acs :=
  let rs := (List.range' 1 31).filter (fun r => bigb K (reg cs r))
  match node_havoc nx0 cs rs with
  | some cs1 =>
      if fresh_ok nx0 cs1 then
        let nx1 := nxt cs1
        let (k', c) := kn_bigsubst K (kn cs1) nx1
        some (with_ss cs1 (mk_ss (pc cs1) cs1.a_ss.s_regs k' (nx1 + c)))
      else none
  | none => none

/-! ### 8.2 visible application ranges and their shadows -/

/-- the tracked entry of one of the kinds `kinds` containing `b+off, +n`. -/
def find_containing (k : List kentry) (ms : List amap) (kinds : List mkind) (b : expr)
    (off : Int) (n : expr) : Option amap :=
  ms.find? (fun m =>
    !is_fog m && kinds.any (fun kd => mkind_eqb m.am_kind kd)
    && xinside k b off n m.am_base 0 m.am_len)

/-- The same through the block context. -/
def find_containingB (bc : bctx) (ms : List amap) (kinds : List mkind) (b : expr)
    (off : Int) (n : expr) : Option amap :=
  ms.find? (fun m =>
    !is_fog m && kinds.any (fun kd => mkind_eqb m.am_kind kd)
    && xinsideB bc b off n m.am_base 0 m.am_len)

/-- `find_containingB` at `mkbc fk` is `find_containing fk`. -/
theorem find_containingB_eqf (fk : List kentry) : find_containingB (mkbc fk) = find_containing fk := by
  funext ms kinds b off n
  simp only [find_containingB, find_containing, xinsideB_eqf]
  try (with_unfolding_all exact rfl)

/-- the shadow interval of the application range `b, b+n` (both multiples of
    8): `shadow_off + b/8, + n/8`, as (base, off, len). -/
def shadow_of (A : atable) (k : List kentry) (b n : expr) : expr × Int × expr :=
  let (sb, sk) := split_lit (eadd (mkSrl k b 3) (.ELit A.shadow_off))
  (sb, sk, mkSrl k n 3)

/-- The same through the block context. -/
def shadow_ofB (A : atable) (bc : bctx) (b n : expr) : expr × Int × expr :=
  let (sb, sk) := split_lit (eadd (mkSrlB bc b 3) (.ELit A.shadow_off))
  (sb, sk, mkSrlB bc n 3)

/-- `shadow_ofB` at `mkbc fk` is `shadow_of fk`. -/
theorem shadow_ofB_eqf (A : atable) (fk : List kentry) :
    shadow_ofB A (mkbc fk) = shadow_of A fk := by
  funext b n
  simp only [shadow_ofB, shadow_of, mkSrlB_eqf]
  try (with_unfolding_all exact rfl)

/-- knowledge that the shadow of `b, b+n` is zero and writable — only when
    that shadow interval lies inside a tracked rw-lazy entry (a shadow map). -/
def shadow_facts (A : atable) (k : List kentry) (ms : List amap) (b n : expr) : List kentry :=
  let (sb, sk, sn) := shadow_of A k b n
  match find_containing k ms [.KRWLAZY] sb sk sn with
  | some _ => [.KWr (SA sb sk) sn, .KZero (SA sb sk) sn]
  | none => []

/-- The same through the block context. -/
def shadow_factsB (A : atable) (bc : bctx) (ms : List amap) (b n : expr) : List kentry :=
  let (sb, sk, sn) := shadow_ofB A bc b n
  match find_containingB bc ms [.KRWLAZY] sb sk sn with
  | some _ => [.KWr (SA sb sk) sn, .KZero (SA sb sk) sn]
  | none => []

/-- `shadow_factsB` at `mkbc fk` is `shadow_facts fk`. -/
theorem shadow_factsB_eqf (A : atable) (fk : List kentry) :
    shadow_factsB A (mkbc fk) = shadow_facts A fk := by
  funext ms b n
  simp only [shadow_factsB, shadow_facts, shadow_ofB_eqf, find_containingB_eqf]
  try (with_unfolding_all exact rfl)

/-- budget charge of a visible range of at most `nhi` bytes: its pages and
    its shadow's pages, rounded outward. -/
def vis_cost (nhi : Int) : Int := nhi + nhi / 8 + 16384

/-- Declare the application range `b, b+n` VISIBLE: b, n multiples of 8,
    n > 0, apart from every visible range so far (so its shadow bytes were
    hidden, hence zero); charges the budget; adds the shadow facts. -/
def vis_add_ref (A : atable) (LIMIT : Int) (cs : acs) (b n : expr)
    (k : List kentry) : Option acs :=
  let k0 := kn cs
  let (bb, bk) := split_lit b
  let (sb, sk, sn) := shadow_of A k0 b n
  match xhi k0 n with
  | some nhi =>
    if (3 ≤ ealign k0 b && 3 ≤ ealign k0 n && flat_x k0 bb bk n
        -- the shadow's own flatness.   reconstructs the shadow's
        -- denotation by `lia` instead; here `shadow_of_val` needs it, and
        -- `node_unvis_ref` already checks it.
        && flat_x k0 sb sk sn
        && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
        && cs.a_vis.all (fun p =>
             let (pb, pk) := split_lit p.1
             flat_x k0 pb pk p.2
             && ranges_apart_x k0 bb bk n pb pk p.2 && ranges_apart_x k0 sb sk sn pb pk p.2)
        -- ghost exemption of `co_zero`: the new shadow must avoid every ghost range
        && cs.a_ghost.all (fun p =>
             let (pb, pk) := split_lit p.1
             flat_x k0 pb pk p.2 && ranges_apart_x k0 sb sk sn pb pk p.2)
        && cs.a_eager + cs.a_abytes + vis_cost nhi ≤ LIMIT) then
      some ⟨mk_ss (pc cs) cs.a_ss.s_regs (shadow_facts A k0 cs.a_maps b n ++ k) (nxt cs),
            cs.a_maps, cs.a_totsz, cs.a_ylo, cs.a_eager,
            (b, n) :: cs.a_vis, cs.a_ghost, cs.a_abytes + vis_cost nhi, cs.a_brk, cs.a_fd,
            cs.a_tidset⟩
    else none
  | none => none

/-- PERF: the same through the block context of the node's knowledge;
    `vis_add_eq`. -/
def vis_add (A : atable) (LIMIT : Int) (cs : acs) (b n : expr)
    (k : List kentry) : Option acs :=
  let k0 := kn cs
  let bc := mkbc k0       -- PERF: block context of the node's knowledge
  let (bb, bk) := split_lit b
  let (sb, sk, sn) := shadow_ofB A bc b n
  match xhiB bc n with
  | some nhi =>
    if (3 ≤ ealignB bc b && 3 ≤ ealignB bc n && flat_xB bc bb bk n
        -- mirror of `vis_add_ref`'s extra shadow-flatness conjunct.
        && flat_xB bc sb sk sn
        && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
        && cs.a_vis.all (fun p =>
             let (pb, pk) := split_lit p.1
             flat_xB bc pb pk p.2
             && ranges_apart_xB bc bb bk n pb pk p.2 && ranges_apart_xB bc sb sk sn pb pk p.2)
        -- ghost exemption of `co_zero`: the new shadow must avoid every ghost range
        && cs.a_ghost.all (fun p =>
             let (pb, pk) := split_lit p.1
             flat_xB bc pb pk p.2 && ranges_apart_xB bc sb sk sn pb pk p.2)
        && cs.a_eager + cs.a_abytes + vis_cost nhi ≤ LIMIT) then
      some ⟨mk_ss (pc cs) cs.a_ss.s_regs (shadow_factsB A bc cs.a_maps b n ++ k) (nxt cs),
            cs.a_maps, cs.a_totsz, cs.a_ylo, cs.a_eager,
            (b, n) :: cs.a_vis, cs.a_ghost, cs.a_abytes + vis_cost nhi, cs.a_brk, cs.a_fd,
            cs.a_tidset⟩
    else none
  | none => none

/-- `vis_add = vis_add_ref`. -/
theorem vis_add_eq (A : atable) (LIMIT : Int) (cs : acs) (b n : expr) (k : List kentry) :
    vis_add A LIMIT cs b n k = vis_add_ref A LIMIT cs b n k := by
  simp only [vis_add, vis_add_ref, ealignB_eqf, flat_xB_eqf, ranges_apart_xB_eqf,
    shadow_factsB_eqf, shadow_ofB_eqf, xhiB_eqf]
  try (with_unfolding_all exact rfl)

/-- `PCaseDisj b1 b2 k1 k2`: case split on a recorded `KDisj` fact between a
    range based at `b1` and one based at `b2` (in either order): child 1 gets
    "range 1 lies below range 2" as the sum fact `KRange (lo2 - lo1) len1lo hi`,
    child 2 the converse. -/
def find_disj (k : List kentry) (b1 b2 : expr) :
    Option (expr × Int × expr × expr × Int × expr) :=
  match k with
  | [] => none
  | .KDisj ⟨c1, o1⟩ n1 ⟨c2, o2⟩ n2 :: r =>
      if (expr_eqb c1 b1 && expr_eqb c2 b2) then some (c1, o1, n1, c2, o2, n2)
      else if (expr_eqb c1 b2 && expr_eqb c2 b1) then some (c2, o2, n2, c1, o1, n1)
      else find_disj r b1 b2
  | _ :: r => find_disj r b1 b2

/-- the fact "`cA+oA, +nA` lies below `cB+oB`": `((cB+oB) - (cA+oA))` in
    `[nA_lo, (cB+oB)_hi]`. -/
def disj_side_fact (k : List kentry) (cA : expr) (oA : Int) (nA : expr) (cB : expr)
    (oB : Int) : Option kentry :=
  match xlo2 k nA, base_range k cB with
  | some n, some (_, bhi) =>
      if (0 ≤ n && n ≤ bhi + oB) then
        some (.KRange (esub (eaddz cB oB) (eaddz cA oA)) n (bhi + oB))
      else none
  | _, _ => none

/-- `PCaseDisj`. -/
def node_casedisj (cs : acs) (b1 b2 : expr) : Option (acs × acs) :=
  let k := kn cs
  match find_disj k b1 b2 with
  | some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2,
            disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, some K1, some K2 => some (add_kn cs [K1], add_kn cs [K2])
      | _, _, _, _ => none
  | none => none

/-- `PShDisj b1 n1 b2 n2`: the SHADOWS of two provably apart, 8-aligned
    application ranges are apart: adds that `KDisj` fact (a memset
    of one region's shadow then keeps the other regions' shadow facts). -/
def node_shdisj_ref (A : atable) (cs : acs) (b1 n1 b2 n2 : expr) : Option acs :=
  let k := kn cs
  let (c1, o1) := split_lit b1
  let (c2, o2) := split_lit b2
  let (sb1, sk1, sn1) := shadow_of A k b1 n1
  let (sb2, sk2, sn2) := shadow_of A k b2 n2
  if (3 ≤ ealign k b1 && 3 ≤ ealign k n1 && 3 ≤ ealign k b2 && 3 ≤ ealign k n2
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      --This tree closes this `match` with `end`; without the
      -- parentheses Lean lets the match swallow the next conjunct, which
      -- would leave `ranges_apart_x` only in the `false` branch.
      && (match xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
         | some h1, some m1, some h2, some m2 => h1 + m1 ≤ zpow 2 47 && h2 + m2 ≤ zpow 2 47
         | _, _, _, _ => false)
      && ranges_apart_x k c1 o1 n1 c2 o2 n2) then
    some (add_kn cs [.KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else none

/-- PERF: the same through the block context of the node's knowledge;
    `node_shdisj_eq`. -/
def node_shdisj (A : atable) (cs : acs) (b1 n1 b2 n2 : expr) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  let (c1, o1) := split_lit b1
  let (c2, o2) := split_lit b2
  let (sb1, sk1, sn1) := shadow_ofB A bc b1 n1
  let (sb2, sk2, sn2) := shadow_ofB A bc b2 n2
  if (3 ≤ ealignB bc b1 && 3 ≤ ealignB bc n1 && 3 ≤ ealignB bc b2 && 3 ≤ ealignB bc n2
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      -- see `node_shdisj_ref` — the parentheses are load-bearing.
      && (match xhiB bc b1, xhiB bc n1, xhiB bc b2, xhiB bc n2 with
         | some h1, some m1, some h2, some m2 => h1 + m1 ≤ zpow 2 47 && h2 + m2 ≤ zpow 2 47
         | _, _, _, _ => false)
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2) then
    some (add_kn cs [.KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else none

/-- `node_shdisj = node_shdisj_ref`. -/
theorem node_shdisj_eq (A : atable) (cs : acs) (b1 n1 b2 n2 : expr) :
    node_shdisj A cs b1 n1 b2 n2 = node_shdisj_ref A cs b1 n1 b2 n2 := by
  simp only [node_shdisj, node_shdisj_ref, ealignB_eqf, flat_xB_eqf, ranges_apart_xB_eqf,
    shadow_ofB_eqf, xhiB_eqf]
  try (with_unfolding_all exact rfl)

/-! ### 8.3 mmap -/

/-- The length request: its page-rounded value as an expression `ne`, a
    numeric lower bound `nlo` > 0 and upper bound `nhi` of `ne`. -/
def mmap_len_ref (cs : acs) : Option (expr × Int × Int) :=
  match reg_lit cs 11 with
  | some len => if 0 < len then some (.ELit (page_up len), page_up len, page_up len) else none
  | none =>
      let le := reg cs 11
      let k := kn cs
      match xlo k le, xhi k le with
      | some lo, some hi =>
          if (0 < lo && 12 ≤ ealign k le && hi ≤ zpow 2 46) then some (le, lo, hi) else none
      | _, _ => none

/-- PERF: the same through the block context of the node's knowledge;
    `mmap_len_eq`. -/
def mmap_len (cs : acs) : Option (expr × Int × Int) :=
  match reg_lit cs 11 with
  | some len => if 0 < len then some (.ELit (page_up len), page_up len, page_up len) else none
  | none =>
      let le := reg cs 11
      let k := kn cs
      let bc := mkbc k       -- PERF: block context of the node's knowledge
      match xloB bc le, xhiB bc le with
      | some lo, some hi =>
          if (0 < lo && 12 ≤ ealignB bc le && hi ≤ zpow 2 46) then some (le, lo, hi) else none
      | _, _ => none

/-- `mmap_len = mmap_len_ref`. -/
theorem mmap_len_eq (cs : acs) : mmap_len cs = mmap_len_ref cs := by
  simp only [mmap_len, mmap_len_ref, ealignB_eqf, xhiB_eqf, xloB_eqf]
  try (with_unfolding_all exact rfl)

/-- facts kept across the creation of a new ledger entry: memory facts
    provably inside the image hull, the stack side `CEIL, 2^64`, or an
    existing tracked entry (all apart from the new region); KImg facts inside
    the hull (caller applies `kimg_clip`). -/
def inside_maps (k : List kentry) : List amap → expr → Int → expr → Bool
  | [], _, _, _ => false
  | m :: rest, b, off, len =>
      (!is_fog m && xinside k b off len m.am_base 0 m.am_len) || inside_maps k rest b off len

/-- The same through the block context. -/
def inside_mapsB (bc : bctx) : List amap → expr → Int → expr → Bool
  | [], _, _, _ => false
  | m :: rest, b, off, len =>
      (!is_fog m && xinsideB bc b off len m.am_base 0 m.am_len) || inside_mapsB bc rest b off len

/-- `inside_mapsB` at `mkbc fk` is `inside_maps fk`. -/
theorem inside_mapsB_eqf (fk : List kentry) : inside_mapsB (mkbc fk) = inside_maps fk := by
  funext ms b off len
  induction ms generalizing b off len with
  | nil => rfl
  | cons m rest ih =>
      simp only [inside_mapsB, inside_maps, ih, xinsideB_eqf]
      try (with_unfolding_all exact rfl)

/-- Is the range safe to keep facts about (stack side, image hull, or inside a
    tracked entry)? -/
def safe_range (A : atable) (k : List kentry) (ms : List amap) (b : expr) (off : Int)
    (len : expr) : Bool :=
  ((match xhi k len, base_range k b with
    | some lh, some (lo, hi) =>
        (CEIL ≤ lo + off && hi + off + lh ≤ two64)               -- stack side
        || (A.img_lo ≤ lo + off && hi + off + lh ≤ A.img_hi)     -- image hull
    | _, _ => false)
   || inside_maps k ms b off len)

/-- The same through the block context. -/
def safe_rangeB (A : atable) (bc : bctx) (ms : List amap) (b : expr) (off : Int)
    (len : expr) : Bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | some lh, some (lo, hi) =>
        (CEIL ≤ lo + off && hi + off + lh ≤ two64)               -- stack side
        || (A.img_lo ≤ lo + off && hi + off + lh ≤ A.img_hi)     -- image hull
    | _, _ => false)
   || inside_mapsB bc ms b off len)

/-- `safe_rangeB` at `mkbc fk` is `safe_range fk`. -/
theorem safe_rangeB_eqf (A : atable) (fk : List kentry) :
    safe_rangeB A (mkbc fk) = safe_range A fk := by
  funext ms b off len
  simp only [safe_rangeB, safe_range, xhiB_eqf, base_rangeB_eqf, inside_mapsB_eqf]
  try (with_unfolding_all exact rfl)

/-- Does the granted entry keep this fact? -/
def grant_keep_b (A : atable) (k : List kentry) (ms : List amap) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, o⟩ w _ => (w ≤ 8) && safe_range A k ms b o (.ELit (w : Int))
  | .KZero ⟨b, o⟩ l => safe_range A k ms b o l
  | .KBlob ⟨b, o⟩ l _ => safe_range A k ms b o l
  | .KImg _ _ => true
  | .KAlign _ _ => true
  | .KRange _ _ _ => true
  | .KDisj _ _ _ _ => true
  | .KWr ⟨b, o⟩ n => safe_range A k ms b o n
  | .KFill ⟨b, o⟩ l _ => safe_range A k ms b o l
  | .KUnk ⟨b, o⟩ l => safe_range A k ms b o l

/-- The same through the block context. -/
def grant_keep_bB (A : atable) (bc : bctx) (ms : List amap) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨b, o⟩ w _ => (w ≤ 8) && safe_rangeB A bc ms b o (.ELit (w : Int))
  | .KZero ⟨b, o⟩ l => safe_rangeB A bc ms b o l
  | .KBlob ⟨b, o⟩ l _ => safe_rangeB A bc ms b o l
  | .KImg _ _ => true
  | .KAlign _ _ => true
  | .KRange _ _ _ => true
  | .KDisj _ _ _ _ => true
  | .KWr ⟨b, o⟩ n => safe_rangeB A bc ms b o n
  | .KFill ⟨b, o⟩ l _ => safe_rangeB A bc ms b o l
  | .KUnk ⟨b, o⟩ l => safe_rangeB A bc ms b o l

/-- `grant_keep_bB` at `mkbc fk` is `grant_keep_b fk`. -/
theorem grant_keep_bB_eqf (A : atable) (fk : List kentry) :
    grant_keep_bB A (mkbc fk) = grant_keep_b A fk := by
  funext ms K
  cases K <;>
    simp only [grant_keep_bB, grant_keep_b, safe_rangeB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- Filter the knowledge down to the facts that survive a grant. -/
def kn_grant_filter (A : atable) (k : List kentry) (ms : List amap) : List kentry :=
  kimg_clip A ((k.filter (grant_keep_b A k ms)))

/-- The same through the block context. -/
def kn_grant_filterB (A : atable) (bc : bctx) (ms : List amap) : List kentry :=
  kimg_clip A (bc.bc_fk.filter (grant_keep_bB A bc ms))

/-- `kn_grant_filterB` at `mkbc fk` is `kn_grant_filter fk`. -/
theorem kn_grant_filterB_eqf (A : atable) (fk : List kentry) :
    kn_grant_filterB A (mkbc fk) = kn_grant_filter A fk := by
  funext ms
  simp only [kn_grant_filterB, kn_grant_filter, bc_fk_mkbc, grant_keep_bB_eqf]
  try (with_unfolding_all exact rfl)

/-- gap slack for a NULL-hint request of (at most) `nhi` bytes:
    `AsanPlacement.free_gap_of_totals`: floor + n + Σ_L size + |L|*(n + 4095) <= ceiling
    ==> a free aligned window at or above the floor exists (the GRANT child is inhabited). -/
def gap_ok (A : atable) (cs : acs) (nhi : Int) : Bool :=
  let cnt := ((A.n_res + cs.a_maps.length : Nat) : Int)
  FLOOR + nhi + cs.a_totsz + cnt * (nhi + 4095) ≤ CEIL

/-- The budget charge of an (eager) grant of `extra` bytes. -/
def budget_ok (LIMIT : Int) (cs : acs) (extra : Int) : Bool :=
  cs.a_eager + cs.a_abytes + extra ≤ LIMIT

/-- disjointness facts of a new entry `nb, +ne` against the tracked entries
    whose base is not a literal (literal ones are separated by ranges). -/
def kdisj_new (ms : List amap) (nb : expr) (ne : expr) : List kentry :=
  ms.flatMap (fun m =>
    if is_fog m then []
    else
      match m.am_base with
      | .ELit _ => []
      | mb => [.KDisj (SA mb 0) m.am_len (SA nb 0) ne])

/-- the state with another ledger list (same as `with_maps` below). -/
def with_maps0 (cs : acs) (ms : List amap) : acs :=
  ACS cs.a_ss ms cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk
    cs.a_fd cs.a_tidset

/-- record a new ledger entry (state AFTER the syscall: pc+4, registers `sr`,
    knowledge `k'`, next variable `nx'`). -/
def add_entry (cs : acs) (sr : List expr) (k' : List kentry) (nx' : Nat)
    (m : amap) (nhi : Int) (eager : Bool) (ylo' : Int) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
    (m :: cs.a_maps) (cs.a_totsz + nhi) ylo'
    (if eager then cs.a_eager + nhi else cs.a_eager)
    cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset

/-- NULL-hint grant (arms P [rw eager], A [rw lazy], B0 [none], B [none lazy]).
    `visible`: the new range is a visible application range (P, A).

    for a SYMBOLIC length the grant also records the JOINT end fact
    base + len <= CEIL (the separate ranges of base and length lose it by the class width);
    consumed by `AX2.end_hi` in `ranges_apart_x`. -/
def null_kend (base ne : expr) (nlo : Int) : List kentry :=
  match ne with
  | .ELit _ => []
  | _ => [.KRange (eadd base ne) (4096 * (KHI / 4096 + 1) + nlo) CEIL]

/-- `PSys YMmap` NULL-hint grant. -/
def mmap_null (A : atable) (nx0 : Nat) (LIMIT : Int) (cs : acs) (kind : mkind)
    (eager visible : Bool) : Option acs :=
  match mmap_len cs with
  | some (ne, nlo, nhi) =>
      if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
          && gap_ok A cs nhi && (!eager || budget_ok LIMIT cs nhi)
          && KHI + 2 * nhi ≤ cs.a_ylo && cs.a_ylo ≤ FLOOR
          && no_holes cs.a_maps) then   -- a NULL-hint grant could land in a hole: consume holes first
        let v := nxt cs
        let base := escale 4096 (.EVar v)
        let kfacts := .KRange (.EVar v) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)
                      :: null_kend base ne nlo ++ kdisj_new cs.a_maps base ne
        let kmem := [.KWr (SA base 0) ne, .KZero (SA base 0) ne]
        let k' := kfacts ++ kn_grant_filter A (kn cs) cs.a_maps
        let cs1 := add_entry cs (sr_upd cs.a_ss.s_regs 10 base) k' (v + 1)
          (AM base ne kind) nhi eager (cs.a_ylo - 2 * nhi)
        if visible then vis_add A LIMIT cs1 base ne (kmem ++ kn cs1) else some cs1
      else none
  | none => none

/-- FIXED request at `reg 10` = b+off: the address must be provably page
    aligned, > 0, above the image and the range below `top` (KHI for new
    entries — the placement invariant — / CEIL inside a tracked entry). -/
def fixed_args (A : atable) (cs : acs) (top : Int) : Option (expr × Int × expr × Int × Int) :=
  let k := kn cs
  let a := reg cs 10
  let (b, off) := split_lit a
  match mmap_len cs, xlo k a, xhi k a with
  | some (ne, nlo, nhi), some alo, some ahi =>
      if (page_aligned k a && 0 < alo && A.img_hi ≤ alo && ahi + nhi ≤ top && flat_x k b off ne) then
        some (b, off, ne, nlo, nhi)
      else none
  | _, _, _ => none

/-- the same expression as a value (`expr_eqb` or equal by exact linear
    arithmetic both ways). -/
def same_val (k : List kentry) (a b : expr) : Bool :=
  if expr_eqb a b then true
  else if lin_ge0 k [(a, (0 : Int))] [(b, (0 : Int))] then
    lin_ge0 k [(b, (0 : Int))] [(a, (0 : Int))]
  else false

/-- the hole token of EXACTLY the range `a, a+ne`. -/
def find_hole (k : List kentry) (ms : List amap) (a ne : expr) : Option amap :=
  ms.find? (fun m => is_hole m && same_val k a m.am_base && same_val k ne m.am_len)

/-- the consumed hole becomes a plain fog token of the same extent (a token may
    stand for an untracked entry in `APS.maps_match`; turning the kind keeps
    that reading, removing the element would not). -/
def unhole (ms : List amap) (h : amap) : List amap :=
  ms.map (fun m => if (is_hole m && amap_eqb m h) then AM m.am_base m.am_len .KFOG else m)

/-- the granted child of a FIXED mmap over a free range, common to both paths of
    `mmap_fixed_free`: `ms0` is the ledger the new entry is added to (`a_maps
    cs` itself, or it with the consumed hole turned into a fog token). -/
def mmap_fixed_grant (A : atable) (LIMIT : Int) (cs : acs) (ms0 : List amap) (b : expr)
    (off : Int) (ne : expr) (nhi : Int) (kind : mkind) (eager visible : Bool) : Option acs :=
  let k := kn cs
  let a := reg cs 10
  let m := AM a ne kind
  let kmem := [.KWr (SA b off) ne, .KZero (SA b off) ne]
  let ksh := if mkind_eqb kind .KRWLAZY then
      cs.a_vis.flatMap (fun p => shadow_facts A k [m] p.1 p.2)
    else []
  let k' := ksh ++ kn_grant_filter A k ms0
  let cs1 := add_entry (with_maps0 cs ms0) cs.a_ss.s_regs k' (nxt cs) m nhi eager cs.a_ylo
  if visible then vis_add A LIMIT cs1 a ne (kmem ++ kn cs1) else some cs1

/-- FIXED over a FREE range (arms C [rw lazy: a SHADOW map], C0 [rw eager],
    D [none lazy], D0 [none eager]).  A new rw-lazy entry gets the shadow
    facts of every visible range whose shadow lies inside it. -/
def mmap_fixed_free (A : atable) (nx0 : Nat) (LIMIT : Int) (cs : acs) (kind : mkind)
    (eager visible : Bool) : Option acs :=
  let k := kn cs
  let a := reg cs 10
  match fixed_args A cs KHI with
  | some (b, off, ne, nlo, nhi) =>
      if (no_fog cs.a_maps
          && cs.a_maps.all (fun m => ranges_apart_x k b off ne m.am_base 0 m.am_len)
          && (!eager || budget_ok LIMIT cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a) then
        mmap_fixed_grant A LIMIT cs cs.a_maps b off ne nhi kind eager visible
      else none
  | none =>
      -- the HOLE path — MAP_FIXED over exactly the free range a refused-DESTROYED `PMmapInH` left;
      -- any OTHER hole must be provably apart from it (it stays a hole)
      match fixed_args A cs CEIL with
      | some (b, off, ne, nlo, nhi) =>
          match find_hole k cs.a_maps a ne with
          | some h =>
              let ms0 := unhole cs.a_maps h
              if (ms0.all (fun m => !is_hole m || ranges_apart_x k b off ne m.am_base 0 m.am_len)
                  && (!eager || budget_ok LIMIT cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a) then
                mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kind eager visible
              else none
          | none => none
      | none => none

/-- facts about `b+off, +n` after the bytes there were RE-ZEROED in place
    (arm F): zero/writability facts stay, values (KWord/KBlob/KFill) go. -/
def kn_rezero (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprep k ub uk un
  k.filter (fun K =>
    match K with
    | .KWord _ _ _ | .KBlob _ _ _ | .KFill _ _ _ => kentry_apart_bp k sp ub uk un K
    | _ => true)

/-- The same through the block context. -/
def kn_rezeroB (bc : bctx) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  let sp := mk_sprepB bc ub uk un
  bc.bc_fk.filter (fun K =>
    match K with
    | .KWord _ _ _ | .KBlob _ _ _ | .KFill _ _ _ => kentry_apart_bpB bc sp ub uk un K
    | _ => true)

/-- `kn_rezeroB` at `mkbc fk` is `kn_rezero fk`. -/
theorem kn_rezeroB_eqf (fk : List kentry) : kn_rezeroB (mkbc fk) = kn_rezero fk := by
  funext ub uk un
  simp only [kn_rezeroB, kn_rezero, mk_sprepB_eqf, bc_fk_mkbc, kentry_apart_bpB_eqf]
  try (with_unfolding_all exact rfl)

/-- `kn_rezero` through `mkbc`. -/
def kn_rezeroM (k : List kentry) (ub : expr) (uk : Int) (un : expr) : List kentry :=
  kn_rezeroB (mkbc k) ub uk un

/-- `kn_rezeroM = kn_rezero`. -/
theorem kn_rezeroM_eq : kn_rezeroM = kn_rezero := by
  funext k ub uk un
  exact congrFun (congrFun (congrFun (kn_rezeroB_eqf k) ub) uk) un

/-- the tracked entry `m` loses its PROT_NONE kind (a slice of it was
    committed / re-protected: its interval is no longer verbatim an element
    of vm_noaccess). -/
def rekind (ms : List amap) (m : amap) : List amap :=
  ms.map (fun m' => if amap_eqb m' m then AM m'.am_base m'.am_len .KRW else m')

/-- FIXED inside a tracked entry (the spec: `Mmap.mmap_spec`'s "wholly inside
    one live mapping" branches, THREE resolutions errno-kept / ok /
    errno-destroyed):
    E  (prot rw, flags 0x32, entry KRW/KNONE/KNONELAZY): commit the slice (eagerly backed; a new VISIBLE range);
    F  (prot rw, flags 0x4032, entry KRWLAZY): re-zero the slice (stays lazy; value facts inside dropped);
    G  (prot none, flags 0x32, entry KRW/KNONE/KNONELAZY): the slice becomes PROT_NONE (facts inside dropped). -/
inductive fixed_in_arm : Type
  | ArmE | ArmF | ArmG
  deriving DecidableEq, Repr

/-- common argument / containment analysis of the three arms:
    (b, off, ne, nlo, nhi, m) with a0 = b+off, `m` the containing entry. -/
def fixed_in_args_ref (A : atable) (cs : acs) (arm : fixed_in_arm) :
    Option (expr × Int × expr × Int × Int × amap) :=
  match fixed_args A cs CEIL with
  | some (b, off, ne, nlo, nhi) =>
      let k := kn cs
      let kinds := match arm with
        | .ArmE => [.KRW, .KNONE, .KNONELAZY]
        | .ArmF => [.KRWLAZY]
        | .ArmG => [.KRW, .KNONE, .KNONELAZY]
      match find_containing k cs.a_maps kinds b off ne with
      | some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10)) then
            some (b, off, ne, nlo, nhi, m)
          else none
      | none => none
  | none => none

/-- PERF: the same through the block context of the node's knowledge;
    `fixed_in_args_eq`. -/
def fixed_in_args (A : atable) (cs : acs) (arm : fixed_in_arm) :
    Option (expr × Int × expr × Int × Int × amap) :=
  match fixed_args A cs CEIL with
  | some (b, off, ne, nlo, nhi) =>
      let k := kn cs
      let bc := mkbc k       -- PERF: block context of the node's knowledge
      let kinds := match arm with
        | .ArmE => [.KRW, .KNONE, .KNONELAZY]
        | .ArmF => [.KRWLAZY]
        | .ArmG => [.KRW, .KNONE, .KNONELAZY]
      match find_containingB bc cs.a_maps kinds b off ne with
      | some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10)) then
            some (b, off, ne, nlo, nhi, m)
          else none
      | none => none
  | none => none

/-- `fixed_in_args = fixed_in_args_ref`. -/
theorem fixed_in_args_eq (A : atable) (cs : acs) (arm : fixed_in_arm) :
    fixed_in_args A cs arm = fixed_in_args_ref A cs arm := by
  cases arm <;> simp only [fixed_in_args, fixed_in_args_ref, find_containingB_eqf] <;>
    try (with_unfolding_all exact rfl)

/-- the OK child. -/
def mmap_fixed_in_ref (A : atable) (LIMIT : Int) (cs : acs) (arm : fixed_in_arm) : Option acs :=
  match fixed_in_args_ref A cs arm with
  | some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs
      if (match arm with | .ArmE => budget_ok LIMIT cs nhi | _ => true) then
        let k' := match arm with
          | .ArmE => kimg_clip A (kn_unfill k b off ne)
          | .ArmF => kimg_clip A (kn_rezero k b off ne)
          | .ArmG => kimg_clip A (kn_cutout k b off ne)
        let ms' := match arm with | .ArmF => cs.a_maps | _ => rekind cs.a_maps m
        let ss := cs.a_ss
        let cs1 := ACS (mk_ss (pc cs + 4) ss.s_regs k' ss.s_next)
                       ms' cs.a_totsz cs.a_ylo
                       (match arm with | .ArmE => cs.a_eager + nhi | _ => cs.a_eager)
                       cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
        match arm with
        | .ArmE => vis_add A LIMIT cs1 (reg cs 10) ne
                     (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1)
        | _ => some cs1
      else none
  | none => none

/-- PERF: the same through the block context of the node's knowledge;
    `mmap_fixed_in_eq`. -/
def mmap_fixed_in (A : atable) (LIMIT : Int) (cs : acs) (arm : fixed_in_arm) : Option acs :=
  match fixed_in_args A cs arm with
  | some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs
      let bc := mkbc k       -- PERF: block context of the node's knowledge
      if (match arm with | .ArmE => budget_ok LIMIT cs nhi | _ => true) then
        let k' := match arm with
          | .ArmE => kimg_clip A (kn_unfillB bc b off ne)
          | .ArmF => kimg_clip A (kn_rezeroB bc b off ne)
          | .ArmG => kimg_clip A (kn_cutoutB bc b off ne)
        let ms' := match arm with | .ArmF => cs.a_maps | _ => rekind cs.a_maps m
        let ss := cs.a_ss
        let cs1 := ACS (mk_ss (pc cs + 4) ss.s_regs k' ss.s_next)
                       ms' cs.a_totsz cs.a_ylo
                       (match arm with | .ArmE => cs.a_eager + nhi | _ => cs.a_eager)
                       cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
        match arm with
        | .ArmE => vis_add A LIMIT cs1 (reg cs 10) ne
                     (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1)
        | _ => some cs1
      else none
  | none => none

/-- `mmap_fixed_in = mmap_fixed_in_ref`. -/
theorem mmap_fixed_in_eq (A : atable) (LIMIT : Int) (cs : acs) (arm : fixed_in_arm) :
    mmap_fixed_in A LIMIT cs arm = mmap_fixed_in_ref A LIMIT cs arm := by
  cases arm <;>
    simp only [mmap_fixed_in, mmap_fixed_in_ref, kn_cutoutB_eqf, kn_rezeroB_eqf,
      kn_unfillB_eqf, fixed_in_args_eq] <;>
    try (with_unfolding_all exact rfl)

/-- `-ENOMEM` as the a0 result word. -/
def ENOMEM_RET : Int := two64 - 12

/-- the REFUSED child of any memory syscall: a0 := -ENOMEM, pc+4, nothing else
    (spec: the `err_ret e` arm of `alt`; model unchanged). -/
def refuse (cs : acs) : acs := set_pc (set_reg cs 10 (.ELit ENOMEM_RET)) (pc cs + 4)

/-- in-place replacement of the tracked entry `m` by `pieces`. -/
def replace_entry (ms : List amap) (m : amap) (pieces : List amap) : List amap :=
  ms.flatMap (fun m' => if amap_eqb m' m then pieces else [m'])

/-- left piece existence fact. -/
def dest_lfact (a mb : expr) (lne : Bool) : kentry :=
  if lne then .KRange (esub a mb) 1 (two64 - 1) else .KRange (esub a mb) 0 0

/-- right piece existence fact. -/
def dest_rfact (a ne mb ml : expr) (rne : Bool) : kentry :=
  if rne then .KRange (esub (eadd mb ml) (eadd a ne)) 1 (two64 - 1)
  else .KRange (esub (eadd mb ml) (eadd a ne)) 0 0

/-- the DESTROYED child (`Mmap.with_mmap_destroyed`: errno AND the range
    `a0, a0+ne` removed from the containing entry by `State.iv_subtract`:
    left piece `(base, a0-base)` iff base < a0, right piece
    `(a0+ne, base+len-(a0+ne))` iff a0+ne < base+len; memory facts meeting
    the range are cut out).  `lne`/`rne` say which pieces exist; the state
    records that choice as two pure facts (difference = 0 / >= 1) so that the
    soundness proof can read the case off the knowledge. -/
def mmap_destroyed_with_ref (A : atable) (hole : Bool) (cs : acs) (b : expr) (off : Int)
    (ne : expr) (m : amap) (lne rne : Bool) : acs :=
  let k := kn cs
  let a := reg cs 10
  let mb := m.am_base
  let ml := m.am_len
  let lp := if lne then [AM mb (esub a mb) m.am_kind] else []
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) m.am_kind] else []
  let hp := if hole then [AM a ne .KHOLE] else []   -- `PMmapInH` remembers the punched range as FREE
  let ss := cs.a_ss
  ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip A (kn_cutout k b off ne))
             ss.s_next)
      (hp ++ replace_entry cs.a_maps m (lp ++ rp)) cs.a_totsz cs.a_ylo cs.a_eager
      cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset

/-- PERF: the same through the block context of the node's knowledge;
    `mmap_destroyed_with_eq`. -/
def mmap_destroyed_with (A : atable) (hole : Bool) (cs : acs) (b : expr) (off : Int)
    (ne : expr) (m : amap) (lne rne : Bool) : acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  let a := reg cs 10
  let mb := m.am_base
  let ml := m.am_len
  let lp := if lne then [AM mb (esub a mb) m.am_kind] else []
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) m.am_kind] else []
  let hp := if hole then [AM a ne .KHOLE] else []   -- `PMmapInH` remembers the punched range as FREE
  let ss := cs.a_ss
  ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip A (kn_cutoutB bc b off ne))
             ss.s_next)
      (hp ++ replace_entry cs.a_maps m (lp ++ rp)) cs.a_totsz cs.a_ylo cs.a_eager
      cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset

/-- `mmap_destroyed_with = mmap_destroyed_with_ref`. -/
theorem mmap_destroyed_with_eq (A : atable) (hole : Bool) (cs : acs) (b : expr) (off : Int)
    (ne : expr) (m : amap) (lne rne : Bool) :
    mmap_destroyed_with A hole cs b off ne m lne rne
      = mmap_destroyed_with_ref A hole cs b off ne m lne rne := by
  simp only [mmap_destroyed_with, mmap_destroyed_with_ref, kn_cutoutB_eqf]
  try (with_unfolding_all exact rfl)

/-- which (left?, right?) combinations the knowledge leaves open (the end of an
    allocator region commit CAN coincide with the region end for one residue
    class and not for another — undecided tests yield both cases, each checked
    separately by `AP.check`, all with the same shape). -/
def dest_cases (cs : acs) (ne : expr) (m : amap) : List (Bool × Bool) :=
  let k := kn cs
  let a := reg cs 10
  let mb := m.am_base
  let ml := m.am_len
  let ls := if lin_ge0 k [(a, -1)] [(mb, 0)] then [true]                  -- mb < a
            else if (expr_eqb a mb || lin_ge0 k [(mb, 0)] [(a, 0)]) then [false]  -- a <= mb
            else [true, false]
  let rs := if lin_ge0 k [(mb, -1), (ml, 0)] [(a, 0), (ne, 0)] then [true]  -- a + ne < mb + ml
            else if lin_ge0 k [(a, 0), (ne, 0)] [(mb, 0), (ml, 0)] then [false]  -- mb + ml <= a + ne
            else [true, false]
  ls.flatMap (fun l => rs.map (fun r => (l, r)))

/-- The DESTROYED child, one state per open case. -/
def mmap_destroyed (A : atable) (hole : Bool) (cs : acs) (b : expr) (off : Int)
    (ne : expr) (m : amap) : List acs :=
  (dest_cases cs ne m).map (fun lr => mmap_destroyed_with A hole cs b off ne m lr.1 lr.2)

/-- common mmap argument gate: a7 = 222, a4 = -1, a5 = 0; (prot, flags, a0 literal 0?). -/
def mmap_gate (cs : acs) : Option (Int × Int × Bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | some 222, some prot, some flags, some m1, some 0 =>
      if !(m1 == two64 - 1) then none
      else some (prot, flags, match reg_lit cs 10 with | some 0 => true | _ => false)
  | _, _, _, _, _ => none

/-- `PMmap kR kG`: NULL-hint (arms P/A/B0/B) or FIXED over a FREE range (arms
    C/C0/D/D0) — two resolutions (refused, granted). -/
def node_mmap2 (A : atable) (nx0 : Nat) (LIMIT : Int) (cs : acs) : Option (acs × acs) :=
  match mmap_gate cs with
  | some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null A nx0 LIMIT cs .KRW true true        -- P
                 | 3, 0x4022 => mmap_null A nx0 LIMIT cs .KRWLAZY false true -- A: lazy rw, visible wholesale
                 | 0, 0x22 => mmap_null A nx0 LIMIT cs .KNONE false false    -- B0
                 | 0, 0x4022 => mmap_null A nx0 LIMIT cs .KNONELAZY false false -- B
                 | _, _ => none
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free A nx0 LIMIT cs .KRWLAZY false false -- C (shadow map)
                 | 3, 0x32 => mmap_fixed_free A nx0 LIMIT cs .KRW true true         -- C0
                 | 0, 0x4032 => mmap_fixed_free A nx0 LIMIT cs .KNONELAZY false false -- D
                 | 0, 0x32 => mmap_fixed_free A nx0 LIMIT cs .KNONE false false      -- D0
                 | _, _ => none
      match g with
      | some csG => some (refuse cs, csG)
      | none => none
  | none => none

/-- `PMmapIn kK kO kD`: FIXED wholly inside one tracked entry — three
    resolutions (refused-kept, ok, refused-destroyed); the destroyed child is a
    LIST of case states (see `dest_cases`). -/
def node_mmapin (A : atable) (nx0 : Nat) (LIMIT : Int) (hole : Bool) (cs : acs) :
    Option (acs × acs × List acs) :=
  match mmap_gate cs with
  | some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => some .ArmE
                 | 3, 0x4032 => some .ArmF
                 | 0, 0x32 => some .ArmG
                 | _, _ => none
      match arm with
      | some arm =>
          match fixed_in_args A cs arm, mmap_fixed_in A LIMIT cs arm with
          | some (b, off, ne, nlo, nhi, m), some csO =>
              some (refuse cs, csO, mmap_destroyed A hole cs b off ne m)
          | _, _ => none
      | none => none
  | _ => none

/-! ### 8.3b mprotect (F2: musl alloc_meta fallback) -/

/-- mprotect(a0 = b+off, a1 = len, a2 = PROT_READ|PROT_WRITE) of a slice of a
    PROT_NONE entry: like arm E (commit; the slice becomes a visible range);
    a0 := 0. -/
def node_mprotect_ref (A : atable) (LIMIT : Int) (cs : acs) : Option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args A cs CEIL with
  | some 226, some 3, some (b, off, ne, nlo, nhi) =>
      let k := kn cs
      match find_containing k cs.a_maps [.KNONE, .KNONELAZY] b off ne with
      | some m =>
          if (budget_ok LIMIT cs nhi && expr_vars_lt (nxt cs) ne
              && expr_vars_lt (nxt cs) (reg cs 10)) then
            let k' := kimg_clip A (kn_unfill k b off ne)
            let ss := cs.a_ss
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.ELit 0)) k' ss.s_next)
                           (rekind cs.a_maps m) cs.a_totsz cs.a_ylo (cs.a_eager + nhi)
                           cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
            vis_add A LIMIT cs1 (reg cs 10) ne
              (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1)
          else none
      | none => none
  | _, _, _ => none

/-- PERF: the same through the block context of the node's knowledge;
    `node_mprotect_eq`. -/
def node_mprotect (A : atable) (LIMIT : Int) (cs : acs) : Option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args A cs CEIL with
  | some 226, some 3, some (b, off, ne, nlo, nhi) =>
      let k := kn cs
      let bc := mkbc k       -- PERF: block context of the node's knowledge
      match find_containingB bc cs.a_maps [.KNONE, .KNONELAZY] b off ne with
      | some m =>
          if (budget_ok LIMIT cs nhi && expr_vars_lt (nxt cs) ne
              && expr_vars_lt (nxt cs) (reg cs 10)) then
            let k' := kimg_clip A (kn_unfillB bc b off ne)
            let ss := cs.a_ss
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.ELit 0)) k' ss.s_next)
                           (rekind cs.a_maps m) cs.a_totsz cs.a_ylo (cs.a_eager + nhi)
                           cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
            vis_add A LIMIT cs1 (reg cs 10) ne
              (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1)
          else none
      | none => none
  | _, _, _ => none

/-- `node_mprotect = node_mprotect_ref`. -/
theorem node_mprotect_eq (A : atable) (LIMIT : Int) (cs : acs) :
    node_mprotect A LIMIT cs = node_mprotect_ref A LIMIT cs := by
  simp only [node_mprotect, node_mprotect_ref, find_containingB_eqf, kn_unfillB_eqf]
  try (with_unfolding_all exact rfl)

/-- `PMprotect kR kG`: mprotect with its two resolutions (refused, granted). -/
def node_mprotect2 (A : atable) (LIMIT : Int) (cs : acs) : Option (acs × acs) :=
  match node_mprotect A LIMIT cs with
  | some csG => some (refuse cs, csG)
  | none => none

/-! ### 8.4 munmap -/

/-- Is `m` the tracked entry of exactly `b, b+n`? -/
def amap_match (k : List kentry) (b : expr) (n : expr) (m : amap) : Bool :=
  !is_fog m && expr_eqb b m.am_base && len_eqb k n m.am_len

/-- The same through the block context. -/
def amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : Bool :=
  !is_fog m && expr_eqb b m.am_base && len_eqbB bc n m.am_len

/-- `amap_matchB` at `mkbc fk` is `amap_match fk`. -/
theorem amap_matchB_eqf (fk : List kentry) : amap_matchB (mkbc fk) = amap_match fk := by
  funext b n m
  simp only [amap_matchB, amap_match, len_eqbB_eqf]
  try (with_unfolding_all exact rfl)

/-- munmap(a0, a1) of exactly one tracked entry (the kernel page-rounds a1).
    Visible ranges inside it are dropped; their shadows must read zero (they
    become hidden lazy bytes again) and the facts about them go. -/
def node_munmap_ref (A : atable) (cs : acs) : Option acs :=
  match reg_lit cs 17, mmap_len cs with
  | some 215, some (ne, nlo, nhi) =>
      let b := reg cs 10
      let k := kn cs
      let (bb, bk) := split_lit b
      let gone := cs.a_vis.filter (fun p =>
        let (pb, pk) := split_lit p.1
        !ranges_apart_x k pb pk p.2 bb bk ne)
      let kept := cs.a_vis.filter (fun p =>
        let (pb, pk) := split_lit p.1
        ranges_apart_x k pb pk p.2 bb bk ne)
      if (cs.a_maps.any (amap_match k b ne) && page_aligned k b && flat_x k bb bk ne
          && (match xhi k b with | some hi => hi + nhi < two64 | none => false)
          && gone.all (fun p =>
               let (pb, pk) := split_lit p.1
               let (sb, sk, sn) := shadow_of A k p.1 p.2
               3 ≤ ealign k p.1 && 3 ≤ ealign k p.2
               && xinside k pb pk p.2 bb bk ne && kzero_x k k sb sk sn)) then
        let k1 := gone.foldl (fun kk p =>
          let (sb, sk, sn) := shadow_of A k p.1 p.2
          kn_unfill kk sb sk sn) (kn_unfill k bb bk ne)
        let ss := cs.a_ss
        some (ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.ELit 0)) k1 ss.s_next)
                 (cs.a_maps.filter (fun m => !amap_match k b ne m))
                 cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                 cs.a_fd cs.a_tidset)
      else none
  | _, _ => none

/-- PERF: the same through the block context of the node's knowledge;
    `node_munmap_eq`. -/
def node_munmap (A : atable) (cs : acs) : Option acs :=
  match reg_lit cs 17, mmap_len cs with
  | some 215, some (ne, nlo, nhi) =>
      let b := reg cs 10
      let k := kn cs
      let bc := mkbc k       -- PERF: block context of the node's knowledge
      let (bb, bk) := split_lit b
      let gone := cs.a_vis.filter (fun p =>
        let (pb, pk) := split_lit p.1
        !ranges_apart_xB bc pb pk p.2 bb bk ne)
      let kept := cs.a_vis.filter (fun p =>
        let (pb, pk) := split_lit p.1
        ranges_apart_xB bc pb pk p.2 bb bk ne)
      if (cs.a_maps.any (amap_matchB bc b ne) && page_alignedB bc b && flat_xB bc bb bk ne
          && (match xhiB bc b with | some hi => hi + nhi < two64 | none => false)
          && gone.all (fun p =>
               let (pb, pk) := split_lit p.1
               let (sb, sk, sn) := shadow_ofB A bc p.1 p.2
               3 ≤ ealignB bc p.1 && 3 ≤ ealignB bc p.2
               && xinsideB bc pb pk p.2 bb bk ne && kzero_xB bc k sb sk sn)) then
        let k1 := gone.foldl (fun kk p =>
          let (sb, sk, sn) := shadow_ofB A bc p.1 p.2
          kn_unfillM kk sb sk sn) (kn_unfillB bc bb bk ne)
        let ss := cs.a_ss
        some (ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.ELit 0)) k1 ss.s_next)
                 (cs.a_maps.filter (fun m => !amap_matchB bc b ne m))
                 cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                 cs.a_fd cs.a_tidset)
      else none
  | _, _ => none

/-- `node_munmap = node_munmap_ref`. -/
theorem node_munmap_eq (A : atable) (cs : acs) : node_munmap A cs = node_munmap_ref A cs := by
  simp only [node_munmap, node_munmap_ref, amap_matchB_eqf, ealignB_eqf, flat_xB_eqf,
    kn_unfillB_eqf, kzero_xB_eqf, page_alignedB_eqf, ranges_apart_xB_eqf, shadow_ofB_eqf,
    xhiB_eqf, xinsideB_eqf, kn_unfillM_eq]
  try (with_unfolding_all exact rfl)

/-! ### 8.5 brk -/

/-- the grow request: a0 = brk + d with d a positive page multiple. -/
def brk_req (cs : acs) : Option Int :=
  match lit_diff (reg cs 10) cs.a_brk with
  | some d => if (0 < d && d % 4096 == 0 && d ≤ zpow 2 40) then some d else none
  | none => none

/-- facts every brk node needs about the current break: page aligned, in
    `(img_hi, KHI - d)`. -/
def brk_base_ok (A : atable) (cs : acs) (d : Int) : Bool :=
  let k := kn cs
  let b := cs.a_brk
  (page_aligned k b
   && match xlo k b, xhi k b with
      | some lo, some hi => 0 < lo && A.img_hi ≤ lo && hi + d ≤ KHI
      | _, _ => false)

/-- the grow is ADMISSIBLE (`Mmap.brk_grow_ok = true`): range free, below the
    ceiling, within budget. -/
def brk_grow_possible (A : atable) (LIMIT : Int) (cs : acs) (d : Int) : Bool :=
  let k := kn cs
  let (bb, bk) := split_lit cs.a_brk
  (brk_base_ok A cs d && no_fog cs.a_maps
   && cs.a_maps.all (fun m =>
        ranges_apart_x k bb bk (.ELit (d + 4096)) m.am_base 0 m.am_len)
        -- + the guard page (`Mmap.brk_grow_ok` frees `lo, hi + page_size`)
   && budget_ok LIMIT cs d)

/-- the grow is provably BLOCKED: the new range overlaps a tracked entry. -/
def brk_grow_blocked (A : atable) (cs : acs) (d : Int) : Bool :=
  let k := kn cs
  let b := cs.a_brk
  (brk_base_ok A cs d
   && cs.a_maps.any (fun m =>
        !is_fog m
        && lin_ge0 k [(m.am_base, -1), (m.am_len, 0)] [(b, 0)]   -- b < base + len
        && lin_ge0 k [(b, d - 1)] [(m.am_base, 0)]))             -- base < b + d

/-- `PSys YBrk`: query, or a provably blocked grow: a0 := brk. -/
def node_brk1 (A : atable) (cs : acs) : Option acs :=
  match reg_lit cs 17 with
  | some 214 =>
      let ok := match reg_lit cs 10 with
                | some 0 => true
                | _ => match brk_req cs with
                       | some d => brk_grow_blocked A cs d
                       | none => false
      if ok then some (set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4)) else none
  | _ => none

/-- `PBrk2`: admissible grow: (blocked child, granted child); the granted
    heap range is a new tracked entry and a visible range. -/
def node_brk2 (A : atable) (LIMIT : Int) (cs : acs) : Option (acs × acs) :=
  match reg_lit cs 17, brk_req cs with
  | some 214, some d =>
      if (brk_grow_possible A LIMIT cs d && expr_vars_lt (nxt cs) (reg cs 10)) then
        let k := kn cs
        let b := cs.a_brk
        let (bb, bk) := split_lit b
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4)
        let k' := kn_grant_filter A k cs.a_maps
        let ss := cs.a_ss
        let csB := ACS (mk_ss (pc cs + 4) ss.s_regs k' ss.s_next)
                       (AM b (.ELit d) .KRW :: cs.a_maps) (cs.a_totsz + d) cs.a_ylo
                       (cs.a_eager + d) cs.a_vis cs.a_ghost cs.a_abytes (reg cs 10) cs.a_fd
                       cs.a_tidset
        match vis_add A LIMIT csB b (.ELit d)
                (.KWr (SA bb bk) (.ELit d) :: .KZero (SA bb bk) (.ELit d) :: kn csB) with
        | some csB' => some (csA, csB')
        | none => none
      else none
  | _, _ => none

/-! ### 8.6 set_tid_address / exit -/

/-- `PSys YSettid`. -/
def node_settid (nx0 : Nat) (cs : acs) : Option acs :=
  match reg_lit cs 17 with
  | some 96 =>
      if (!cs.a_tidset && fresh_ok nx0 cs) then
        let v := nxt cs
        let ss := cs.a_ss
        some (ACS (mk_ss (pc cs + 4) (sr_upd ss.s_regs 10 (.EVar v))
                        (.KRange (.EVar v) 1 (PID_MAX - 1) :: ss.s_know) (v + 1))
                  cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes
                  cs.a_brk cs.a_fd true)
      else none
  | _ => none

/-- `PSys YExit`: the exit code (low byte of a0). -/
def node_exit (cs : acs) : Option Int :=
  match reg_lit cs 17, reg_lit cs 10 with
  | some 94, some code => some (zland code 255)
  | some 93, some code => some (zland code 255)
  | _, _ => none

/-! ### 8.6b fog / ghost / brk-havoc nodes -/

/-- Set the `i`-th element (no-op out of range). -/
def list_set_nth {T : Type} (i : Nat) (x : T) (l : List T) : List T :=
  match l, i with
  | [], _ => []
  | _ :: r, 0 => x :: r
  | y :: r, i' + 1 => y :: list_set_nth i' x r

/-- Insert `x` at position `i` (append if `i` is past the end). -/
def list_insert_nth {T : Type} (i : Nat) (x : T) (l : List T) : List T :=
  match i, l with
  | 0, _ => x :: l
  | i' + 1, y :: r => y :: list_insert_nth i' x r
  | _ + 1, [] => [x]

/-- A fog token of size `sz`. -/
def fog_token (sz : Int) : amap := AM (.ELit 0) (.ELit sz) .KFOG

/-- Replace the ledger. -/
def with_maps (cs : acs) (ms : List amap) : acs :=
  ACS cs.a_ss ms cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk
    cs.a_fd cs.a_tidset

/-- `PFog i sz`: the i-th tracked entry (not a token, length provably <= sz,
    `0 <= sz < 2^64`) becomes a token. -/
def node_fog (cs : acs) (i : Nat) (sz : Int) : Option acs :=
  match cs.a_maps[i]? with
  | some m =>
      if (!is_fog m && 0 ≤ sz && sz < two64
          && (match xhi (kn cs) m.am_len with | some h => h ≤ sz | none => false)) then
        some (with_maps cs (list_set_nth i (fog_token sz) cs.a_maps))
      else none
  | none => none

/-- `PFogNew i sz`: a token denoting NO entry, inserted at position i. -/
def node_fognew (cs : acs) (i : Nat) (sz : Int) : Option acs :=
  if (i ≤ cs.a_maps.length && 0 ≤ sz && sz < two64) then
    some (with_maps cs (list_insert_nth i (fog_token sz) cs.a_maps))
  else none

/-- `PGhost b n`: over-approximate the budgeted set by the app range `b, b+n`. -/
def node_ghost (LIMIT : Int) (cs : acs) (b n : expr) : Option acs :=
  match xhi (kn cs) n with
  | some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
          && cs.a_eager + cs.a_abytes + vis_cost nhi ≤ LIMIT) then
        some (ACS cs.a_ss cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis
                 (cs.a_ghost ++ [(b, n)]) (cs.a_abytes + vis_cost nhi) cs.a_brk cs.a_fd
                 cs.a_tidset)
      else none
  | none => none

/-- Is the pair exactly `(b, n)`? -/
def vis_here (b n : expr) (p : expr × expr) : Bool := expr_eqb p.1 b && expr_eqb p.2 n

/-- `PUnvis b n`: the visible range (b, n) (syntactically an element of `a_vis`)
    becomes a ghost range: every memory fact about it and about its shadow is
    dropped, its shadow must read zero (it turns hidden and lazy shadow bytes
    outside every visible/ghost reason must be zero, `co_zero`). -/
def node_unvis_ref (A : atable) (cs : acs) (b n : expr) : Option acs :=
  let k := kn cs
  let (bb, bk) := split_lit b
  let (sb, sk, sn) := shadow_of A k b n
  match xhi k b, xhi k n with
  | some bh, some nh =>
      if (cs.a_vis.any (vis_here b n)
          && 3 ≤ ealign k b && 3 ≤ ealign k n && flat_x k bb bk n && bh + nh ≤ CEIL
          && flat_x k sb sk sn && kzero_x k k sb sk sn) then
        let k1 := kn_unfill k bb bk n
        let k2 := kn_unfill k1 sb sk sn
        let ss := cs.a_ss
        some (ACS (mk_ss ss.s_pc ss.s_regs k2 ss.s_next)
                  cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager
                  (cs.a_vis.filter (fun p => !vis_here b n p)) (cs.a_ghost ++ [(b, n)])
                  cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
      else none
  | _, _ => none

/-- PERF: the same through the block context of the node's knowledge;
    `node_unvis_eq`. -/
def node_unvis (A : atable) (cs : acs) (b n : expr) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  let (bb, bk) := split_lit b
  let (sb, sk, sn) := shadow_ofB A bc b n
  match xhiB bc b, xhiB bc n with
  | some bh, some nh =>
      if (cs.a_vis.any (vis_here b n)
          && 3 ≤ ealignB bc b && 3 ≤ ealignB bc n && flat_xB bc bb bk n && bh + nh ≤ CEIL
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn) then
        let k1 := kn_unfillB bc bb bk n
        let k2 := kn_unfillM k1 sb sk sn
        let ss := cs.a_ss
        some (ACS (mk_ss ss.s_pc ss.s_regs k2 ss.s_next)
                  cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager
                  (cs.a_vis.filter (fun p => !vis_here b n p)) (cs.a_ghost ++ [(b, n)])
                  cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
      else none
  | _, _ => none

/-- `node_unvis = node_unvis_ref`. -/
theorem node_unvis_eq (A : atable) (cs : acs) (b n : expr) :
    node_unvis A cs b n = node_unvis_ref A cs b n := by
  simp only [node_unvis, node_unvis_ref, ealignB_eqf, flat_xB_eqf, kn_unfillB_eqf,
    kzero_xB_eqf, shadow_ofB_eqf, xhiB_eqf, kn_unfillM_eq]
  try (with_unfolding_all exact rfl)

/-- `PHavocBrk lo hi`: forget the break: `a_brk := a fresh variable`, known to
    lie in `[lo, hi]` (which must contain the current break's range). -/
def node_havocbrk (nx0 : Nat) (cs : acs) (lo hi : Int) : Option acs :=
  match xlo (kn cs) cs.a_brk, xhi (kn cs) cs.a_brk with
  | some l, some h =>
      if (fresh_ok nx0 cs && lo ≤ l && h ≤ hi) then
        let v := nxt cs
        let ss := cs.a_ss
        some (ACS (mk_ss ss.s_pc ss.s_regs (.KRange (.EVar v) lo hi :: ss.s_know) (v + 1))
                  cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes
                  (.EVar v) cs.a_fd cs.a_tidset)
      else none
  | _, _ => none

/-- `PIntro lo hi`: introduce a FRESH variable (nxt) known to lie in `[lo, hi]`
    (09-01: a start-up variant in which a musl page is NOT mapped gives the
    page's plan variable the same range fact the granting variant has, so that
    the fact survives the syntactic meet of the hand-off states; sound because
    `lo <= hi` leaves a witness). -/
def node_intro (nx0 : Nat) (cs : acs) (lo hi : Int) : Option acs :=
  if (fresh_ok nx0 cs && 0 ≤ lo && lo ≤ hi && hi < two64) then
    let v := nxt cs
    let ss := cs.a_ss
    some (with_ss cs (mk_ss ss.s_pc ss.s_regs (.KRange (.EVar v) lo hi :: ss.s_know) (v + 1)))
  else none

/-- `PSpin`: the sealed runtime's silent self-loop `jal x0, 0` (word 0x6f) at
    the current (literal) pc — the configuration spins forever, emitting nothing. -/
def SPIN_WORD : Int := 0x6f

/-- `PSpin`. -/
def node_spin (segs : List Segment) (cs : acs) : Bool :=
  (0 ≤ pc cs && pc cs + 4 < two64 &&
   match fetch_word segs (Z_to_bv 64 (pc cs)) with
   | some w => bv_unsigned w == SPIN_WORD
   | none => false)

/-! ### 8.7 extension nodes -/

/-- common part of the three memset-like summaries: dst = a0, byte c = a1 mod 256
    (literal), n = a2 (literal or symbolic, bounded); dst range writable by a
    KWr fact (hence visible and overlay-defined) OR a literal range inside the
    image hull (then `KImg` is cut around it); post: `after_call` with a0 kept,
    the range havoc'd and re-described: KZero (c = 0) / KFill (c <> 0). -/
def summary_fill_ref (A : atable) (nx0 : Nat) (cs : acs) (entry : Int) (cmax : Int) : Option acs :=
  let k := kn cs
  if !(pc cs == entry) then none
  else
    match ret_lit cs, reg_lit cs 11 with
    | some ret, some c =>
        if !(c < cmax) then none
        else
          let dst := reg cs 10
          let ne := reg cs 12
          let (db, dk) := split_lit dst
          let c8 := c % 256
          match xlo k ne, xhi k ne, xhi k dst with
          | some nlo, some nhi, some dhi =>
              if (0 ≤ nlo && nhi ≤ zpow 2 40 && dhi + nhi < two64) then
                if (nhi == 0) then after_call nx0 cs ret (some dst) k
                else if (c8 == 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne) then
                  after_call nx0 cs ret (some dst) k
                else
                  match (if off_image_x A k db dk ne then some k
                         else match dst, ne with
                              | .ELit d, .ELit n => some (kimg_cut k (d % two64) n)
                              | _, _ => none) with
                  | none => none
                  | some k0 =>
                      if kwritable_x k k db dk ne then
                        let k1 := kn_havoc k0 db dk ne
                        let k2 := if 0 < nlo then
                                    (if c8 == 0 then .KZero (SA db dk) ne
                                     else .KFill (SA db dk) ne c8) :: k1
                                  else k1
                        after_call nx0 cs ret (some dst) k2
                      else none
              else none
          | _, _, _ => none
    | _, _ => none

/-- PERF: the same through the block context of the node's knowledge;
    `summary_fill_eq`. -/
def summary_fill (A : atable) (nx0 : Nat) (cs : acs) (entry : Int) (cmax : Int) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  if !(pc cs == entry) then none
  else
    match ret_lit cs, reg_lit cs 11 with
    | some ret, some c =>
        if !(c < cmax) then none
        else
          let dst := reg cs 10
          let ne := reg cs 12
          let (db, dk) := split_lit dst
          let c8 := c % 256
          match xloB bc ne, xhiB bc ne, xhiB bc dst with
          | some nlo, some nhi, some dhi =>
              if (0 ≤ nlo && nhi ≤ zpow 2 40 && dhi + nhi < two64) then
                if (nhi == 0) then after_call nx0 cs ret (some dst) k
                else if (c8 == 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne) then
                  after_call nx0 cs ret (some dst) k
                else
                  match (if off_image_xB A bc db dk ne then some k
                         else match dst, ne with
                              | .ELit d, .ELit n => some (kimg_cut k (d % two64) n)
                              | _, _ => none) with
                  | none => none
                  | some k0 =>
                      if kwritable_xB bc k db dk ne then
                        let k1 := kn_havocM k0 db dk ne
                        let k2 := if 0 < nlo then
                                    (if c8 == 0 then .KZero (SA db dk) ne
                                     else .KFill (SA db dk) ne c8) :: k1
                                  else k1
                        after_call nx0 cs ret (some dst) k2
                      else none
              else none
          | _, _, _ => none
    | _, _ => none

/-- `summary_fill = summary_fill_ref`. -/
theorem summary_fill_eq (A : atable) (nx0 : Nat) (cs : acs) (entry : Int) (cmax : Int) :
    summary_fill A nx0 cs entry cmax = summary_fill_ref A nx0 cs entry cmax := by
  simp only [summary_fill, summary_fill_ref, kwritable_xB_eqf, kzero_xB_eqf,
    off_image_xB_eqf, xhiB_eqf, xloB_eqf, kn_havocM_eq]
  try (with_unfolding_all exact rfl)

/-- Literal-length copy support: the source `sb+sk, +n` read back from the
    knowledge in 8-byte words (tail bytewise) as expressions; `none` if some
    piece is unknown. -/
def copy_facts (segs : List Segment) (fuel : Nat) (k : List kentry) (sb : expr) (sk : Int)
    (db : expr) (dk : Int) (n : Int) : Option (List kentry) :=
  match fuel with
  | 0 => some []
  | f + 1 =>
      if (8 ≤ n &&
          (match kread8e segs k sb sk with
           | some _ => true
           | none => match kread_bytes segs 8 k sb sk with | some _ => true | none => false)) then
        match (match kread8e segs k sb sk with
               | some v => some v
               | none => match kread_bytes segs 8 k sb sk with
                         | some bs => some (.ELit (zbytes_le_to_Z bs))
                         | none => none),
              copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8) with
        | some v, some rest => some (.KWord (SA db dk) 8 v :: rest)
        | _, _ => none
      else if 1 ≤ n then   -- (R9) also the byte-wise fallback when an 8-byte piece is not known as a whole
        match know_lookup segs k sb sk 1 false [] [],
              copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1) with
        | .LHit v [] _, some rest => some (.KWord (SA db dk) 1 v :: rest)
        | _, _ => none
      else some []

/-- The same through the block context. -/
def copy_factsB (segs : List Segment) (bc : bctx) (fuel : Nat) (sb : expr) (sk : Int)
    (db : expr) (dk : Int) (n : Int) : Option (List kentry) :=
  match fuel with
  | 0 => some []
  | f + 1 =>
      if (8 ≤ n &&
          (match kread8eB segs bc sb sk with
           | some _ => true
           | none => match kread_bytesB segs bc 8 sb sk with | some _ => true | none => false)) then
        match (match kread8eB segs bc sb sk with
               | some v => some v
               | none => match kread_bytesB segs bc 8 sb sk with
                         | some bs => some (.ELit (zbytes_le_to_Z bs))
                         | none => none),
              copy_factsB segs bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | some v, some rest => some (.KWord (SA db dk) 8 v :: rest)
        | _, _ => none
      else if 1 ≤ n then   -- (R9) also the byte-wise fallback when an 8-byte piece is not known as a whole
        match know_lookupB segs bc sb sk 1 false [] [],
              copy_factsB segs bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | .LHit v [] _, some rest => some (.KWord (SA db dk) 1 v :: rest)
        | _, _ => none
      else some []

/-- `copy_factsB` at `mkbc fk`, at fixed fuel. -/
theorem copy_factsB_eqf' (segs : List Segment) (fk : List kentry) (fuel : Nat) :
    copy_factsB segs (mkbc fk) fuel = copy_facts segs fuel fk := by
  funext sb sk db dk n
  induction fuel generalizing sb sk db dk n with
  | zero => rfl
  | succ f ih =>
      simp only [copy_factsB, copy_facts, kread8eB_eqf, kread_bytesB_eqf', know_lookupB_eqf, ih]
      try (with_unfolding_all exact rfl)

/-- `copy_factsB` at `mkbc fk`. -/
theorem copy_factsB_eqf (segs : List Segment) (fk : List kentry) :
    copy_factsB segs (mkbc fk) = fun fuel => copy_facts segs fuel fk := by
  funext fuel
  exact copy_factsB_eqf' segs fk fuel

/-- exact transport of a LEADING BLOB
    through a havoc-fallback copy.  When the source range `sb+sk, +n` starts with a fact
    `KBlob (SA sb sk) (ELit n0) j` (`0 < n0 <= nlo`), the destination's first n0 bytes ARE blob j:
    `KBlob (SA db dk) (ELit n0) j` is put in front of the `KUnk` describing the rest (cli.c's
    grow_buf memcpy moves the file's chunk 0 — the header bytes — from buffer to buffer). -/
def kblob_prefix (k : List kentry) (sb : expr) (sk : Int) (db : expr) (dk : Int)
    (nlo : Int) : List kentry :=
  match k.find? (fun K =>
    match K with
    | .KBlob ⟨b, o⟩ (.ELit n0) _ => expr_eqb b sb && o == sk && 0 < n0 && n0 ≤ nlo
    | _ => false) with
  | some (.KBlob _ (.ELit n0) j) => [.KBlob (SA db dk) (.ELit n0) j]
  | _ => []

/-- internal_memcpy(d = a0, s = a1, n = a2): n literal or symbolic (bounded);
    dst writable (KWr), the two ranges apart; the source must be described by
    the knowledge: ONE covering KZero range (then dst gets KZero), or — n
    literal <= 2048 — readable piecewise (dst gets the read expressions).
    Post: `after_call`, a0 kept. -/
def summary_copy_ref (A : atable) (segs : List Segment) (nx0 : Nat) (cs : acs)
    (entry : Int) : Option acs :=
  let k := kn cs
  if !(pc cs == entry) then none
  else
    match ret_lit cs with
    | some ret =>
        let dst := reg cs 10
        let src := reg cs 11
        let ne := reg cs 12
        let (db, dk) := split_lit dst
        let (sb, sk) := split_lit src
        match xlo k ne, xhi k ne, xhi k dst, xhi k src with
        | some nlo, some nhi, some dhi, some shi =>
            if (0 ≤ nlo && nhi ≤ zpow 2 40 && dhi + nhi < two64 && shi + nhi < two64) then
              if nhi == 0 then after_call nx0 cs ret (some dst) k
              else
                match (if off_image_x A k db dk ne then some k
                       else match dst, ne with
                            | .ELit d, .ELit n => some (kimg_cut k (d % two64) n)
                            | _, _ => none) with
                | none => none
                | some k0 =>
                    if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne) then
                      let k1 := kn_havoc k0 db dk ne
                      -- HAVOC-SOURCE fallback: the source is merely known writable (hence
                      -- mapped and readable) and flat: the destination range is havoc'd; for a LITERAL
                      -- length that is a multiple of 8 and <= 256 the destination words are re-described by
                      -- fresh variables `KWord (dst+8i) 8 (EVar (nx+NCS+i))` (so later loads succeed);
                      -- otherwise no facts are added
                      let nx := nxt cs
                      let words := if (nlo == nhi && nhi % 8 == 0 && nhi ≤ 256 && 0 < nhi) then
                                     (nhi / 8).toNat else 0
                      let kfresh := (List.range words).map (fun i =>
                        .KWord (SA db (dk + 8 * (i : Int))) 8 (.EVar (nx + NCS + i)))
                      let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne) then
                                         after_call2 nx0 cs ret (some dst)
                                           (kfresh ++ kblob_prefix k sb sk db dk nlo
                                            ++ (if 0 < nlo then .KUnk (SA db dk) ne :: k1 else k1))
                                           words
                                       else none
                      if (0 < nlo && kzero_x k k sb sk ne) then
                        after_call nx0 cs ret (some dst) (.KZero (SA db dk) ne :: k1)
                      else
                        match ne with
                        | .ELit _ =>
                            if (nhi ≤ 2048 && flat_x k sb sk ne) then
                              match copy_facts segs nhi.toNat k sb sk db dk nhi with
                              | some kc => after_call nx0 cs ret (some dst) (kc ++ k1)
                              | none => havoc_src
                            else havoc_src
                        | _ => havoc_src
                    else none
            else none
        | _, _, _, _ => none
    | none => none

/-- PERF: the same through the block context of the node's knowledge;
    `summary_copy_eq`. -/
def summary_copy (A : atable) (segs : List Segment) (nx0 : Nat) (cs : acs)
    (entry : Int) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  if !(pc cs == entry) then none
  else
    match ret_lit cs with
    | some ret =>
        let dst := reg cs 10
        let src := reg cs 11
        let ne := reg cs 12
        let (db, dk) := split_lit dst
        let (sb, sk) := split_lit src
        match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
        | some nlo, some nhi, some dhi, some shi =>
            if (0 ≤ nlo && nhi ≤ zpow 2 40 && dhi + nhi < two64 && shi + nhi < two64) then
              if nhi == 0 then after_call nx0 cs ret (some dst) k
              else
                match (if off_image_xB A bc db dk ne then some k
                       else match dst, ne with
                            | .ELit d, .ELit n => some (kimg_cut k (d % two64) n)
                            | _, _ => none) with
                | none => none
                | some k0 =>
                    if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne) then
                      let k1 := kn_havocM k0 db dk ne
                      let nx := nxt cs
                      let words := if (nlo == nhi && nhi % 8 == 0 && nhi ≤ 256 && 0 < nhi) then
                                     (nhi / 8).toNat else 0
                      let kfresh := (List.range words).map (fun i =>
                        .KWord (SA db (dk + 8 * (i : Int))) 8 (.EVar (nx + NCS + i)))
                      let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne) then
                                         after_call2 nx0 cs ret (some dst)
                                           (kfresh ++ kblob_prefix k sb sk db dk nlo
                                            ++ (if 0 < nlo then .KUnk (SA db dk) ne :: k1 else k1))
                                           words
                                       else none
                      if (0 < nlo && kzero_xB bc k sb sk ne) then
                        after_call nx0 cs ret (some dst) (.KZero (SA db dk) ne :: k1)
                      else
                        match ne with
                        | .ELit _ =>
                            if (nhi ≤ 2048 && flat_xB bc sb sk ne) then
                              match copy_factsB segs bc nhi.toNat sb sk db dk nhi with
                              | some kc => after_call nx0 cs ret (some dst) (kc ++ k1)
                              | none => havoc_src
                            else havoc_src
                        | _ => havoc_src
                    else none
            else none
        | _, _, _, _ => none
    | none => none

/-- `summary_copy = summary_copy_ref`. -/
theorem summary_copy_eq (A : atable) (segs : List Segment) (nx0 : Nat) (cs : acs) (entry : Int) :
    summary_copy A segs nx0 cs entry = summary_copy_ref A segs nx0 cs entry := by
  simp only [summary_copy, summary_copy_ref, copy_factsB_eqf, flat_xB_eqf, kwritable_xB_eqf,
    kzero_xB_eqf, off_image_xB_eqf, ranges_apart_xB_eqf, xhiB_eqf, xloB_eqf, kn_havocM_eq]
  try (with_unfolding_all exact rfl)

/-- mem_is_zero(beg = a0, size = a1) at `x_memiszero`, ONE-SIDED: the whole
    range `beg, beg+size` must read as zero bytes (one covering KZero fact;
    size >= 1 at every call site), size <= 2^40; the 16-byte frame below sp
    writable and apart from the range.  Post: a0 := 1, caller-saved fresh,
    the frame havoc'd.  (preconditions as required by its proof) -/
def summary_miz_ref (A : atable) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  if !(pc cs == A.x_memiszero) then none
  else
    match ret_lit cs with
    | some ret =>
        let beg := reg cs 10
        let ne := reg cs 11
        let sp := reg cs 2
        let (bb, bk) := split_lit beg
        let spm := eaddz sp (-16)
        let (qb, qk) := split_lit spm
        match xlo k ne, xhi k ne, xhi k beg, xlo k sp, xhi k sp with
        | some nlo, some nhi, some bhi, some splo, some sphi =>
            if (0 ≤ nlo && nhi ≤ zpow 2 40 && bhi + nhi + 8 ≤ two64
                && 16 ≤ splo && sphi < two64
                && kwritable k k qb qk 16
                && ranges_apart_x k qb qk (.ELit 16) bb bk ne && kzero_x k k bb bk ne) then
              after_call nx0 cs ret (some (.ELit 1)) (kn_havoc k qb qk (.ELit 16))
            else none
        | _, _, _, _, _ => none
    | none => none

/-- PERF: the same through the block context of the node's knowledge;
    `summary_miz_eq`. -/
def summary_miz (A : atable) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  if !(pc cs == A.x_memiszero) then none
  else
    match ret_lit cs with
    | some ret =>
        let beg := reg cs 10
        let ne := reg cs 11
        let sp := reg cs 2
        let (bb, bk) := split_lit beg
        let spm := eaddz sp (-16)
        let (qb, qk) := split_lit spm
        match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
        | some nlo, some nhi, some bhi, some splo, some sphi =>
            if (0 ≤ nlo && nhi ≤ zpow 2 40 && bhi + nhi + 8 ≤ two64
                && 16 ≤ splo && sphi < two64
                && kwritableB bc k qb qk 16
                && ranges_apart_xB bc qb qk (.ELit 16) bb bk ne && kzero_xB bc k bb bk ne) then
              after_call nx0 cs ret (some (.ELit 1)) (kn_havocB bc qb qk (.ELit 16))
            else none
        | _, _, _, _, _ => none
    | none => none

/-- `summary_miz = summary_miz_ref`. -/
theorem summary_miz_eq (A : atable) (nx0 : Nat) (cs : acs) :
    summary_miz A nx0 cs = summary_miz_ref A nx0 cs := by
  simp only [summary_miz, summary_miz_ref, kn_havocB_eqf, kwritableB_eqf, kzero_xB_eqf,
    ranges_apart_xB_eqf, xhiB_eqf, xloB_eqf]
  try (with_unfolding_all exact rfl)

/-- a `KImg lo hi` entry covering the absolute range `a, b` (so the overlay is
    undefined there: image bytes). -/
def img_cov (k : List kentry) (a b : Int) : Bool :=
  k.any (fun K =>
    match K with | .KImg lo hi => lo ≤ a && b ≤ hi | _ => false)

/-- The same through the block context. -/
def img_covB (bc : bctx) (a b : Int) : Bool :=
  bc.bc_fk.any (fun K =>
    match K with | .KImg lo hi => lo ≤ a && b ≤ hi | _ => false)

/-- `img_covB` at `mkbc fk` is `img_cov fk`. -/
theorem img_covB_eqf (fk : List kentry) : img_covB (mkbc fk) = img_cov fk := by
  funext a b
  simp only [img_covB, img_cov, bc_fk_mkbc]
  try (with_unfolding_all exact rfl)

/-- "<sealed>" as a little-endian 8-byte word. -/
def SEALED_W : Int := 0x3e64656c6165733c

/-- sanitizer internal_strncpy(dst = a0, src = a1, n = a2) at `x_istrncpy` for
    its ONLY use: src = `x_sealed` (the image string "<sealed>\0", overlay
    undefined there), n = 4095; dst writable (off the image, or a literal range
    inside it: `KImg` cut) and apart from the source.  Post: `after_call`, a0
    kept, dst[0,8) = "<sealed>", dst[8,4095) = 0. -/
def summary_istrncpy_ref (A : atable) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  if !(pc cs == A.x_istrncpy) then none
  else
    match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
    | some ret, some src, some n =>
        if !(src == A.x_sealed && n == 4095) then none
        else
          let dst := reg cs 10
          let (db, dk) := split_lit dst
          match xhi k dst with
          | some dhi =>
              match (if off_image_x A k db dk (.ELit 4095) then some k
                     else match dst with
                          | .ELit d => some (kimg_cut k (d % two64) 4095)
                          | _ => none) with
              | none => none
              | some k0 =>
                  if (dhi + 4095 < two64 && 0 ≤ A.x_sealed && A.x_sealed + 9 < two64
                      && kwritable_x k k db dk (.ELit 4095)
                      && img_cov k0 A.x_sealed (A.x_sealed + 9)
                      && ranges_apart_x k db dk (.ELit 4095) (.ELit 0) A.x_sealed (.ELit 9)) then
                    after_call nx0 cs ret (some dst)
                      (.KWord (SA db dk) 8 (.ELit SEALED_W)
                       :: .KZero (SA db (dk + 8)) (.ELit 4087)
                       :: kn_havoc k0 db dk (.ELit 4095))
                  else none
          | none => none
    | _, _, _ => none

/-- PERF: the same through the block context of the node's knowledge;
    `summary_istrncpy_eq`. -/
def summary_istrncpy (A : atable) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  if !(pc cs == A.x_istrncpy) then none
  else
    match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
    | some ret, some src, some n =>
        if !(src == A.x_sealed && n == 4095) then none
        else
          let dst := reg cs 10
          let (db, dk) := split_lit dst
          match xhiB bc dst with
          | some dhi =>
              match (if off_image_xB A bc db dk (.ELit 4095) then some k
                     else match dst with
                          | .ELit d => some (kimg_cut k (d % two64) 4095)
                          | _ => none) with
              | none => none
              | some k0 =>
                  if (dhi + 4095 < two64 && 0 ≤ A.x_sealed && A.x_sealed + 9 < two64
                      && kwritable_xB bc k db dk (.ELit 4095)
                      && img_cov k0 A.x_sealed (A.x_sealed + 9)
                      && ranges_apart_xB bc db dk (.ELit 4095) (.ELit 0) A.x_sealed (.ELit 9)) then
                    after_call nx0 cs ret (some dst)
                      (.KWord (SA db dk) 8 (.ELit SEALED_W)
                       :: .KZero (SA db (dk + 8)) (.ELit 4087)
                       :: kn_havocM k0 db dk (.ELit 4095))
                  else none
          | none => none
    | _, _, _ => none

/-- `summary_istrncpy = summary_istrncpy_ref`. -/
theorem summary_istrncpy_eq (A : atable) (nx0 : Nat) (cs : acs) :
    summary_istrncpy A nx0 cs = summary_istrncpy_ref A nx0 cs := by
  simp only [summary_istrncpy, summary_istrncpy_ref, kwritable_xB_eqf, off_image_xB_eqf,
    ranges_apart_xB_eqf, xhiB_eqf, kn_havocM_eq]
  try (with_unfolding_all exact rfl)

/-- SizeClassAllocator64::PopulateFreeArray's fill loop at `x_popfree`
    (head) .. +32 (exit): a0 = i, a1 = e (free-array END address: symbolic),
    a2 = c, s5 = s, s3 = n with i, c, s, n LITERAL, cnt := n - i >= 1 cells:
    cell j (address e - 4n + 4j, j < cnt) := u32 ((c + (cnt-1-j)*s) / 16).
    The node writes `KWord` facts for the `K` highest cells only (the ones the
    allocator pops next; `args` = `[ELit K]`, K <= cnt) and `KUnk` below them.
    Exit registers: a0 = n, a2 = c + cnt*s, a4 = (c + (cnt-1)*s)/16,
    a5 = e - 4n; everything else unchanged (no fresh variables). -/
def popfree_facts (lb : expr) (lk : Int) (cnt c s : Int) (K : Nat) : List kentry :=
  (List.range K).map (fun (t : Nat) =>
    .KWord (SA lb (lk + 4 * (cnt - 1 - (t : Int)))) 4 (.ELit ((c + (t : Int) * s) / 16)))

/-- `PX XPopfree` summary. -/
def summary_popfree (A : atable) (nx0 : Nat) (cs : acs) (args : List expr) : Option acs :=
  let k := kn cs
  if !(pc cs == A.x_popfree) then none
  else
    match args, reg_lit cs 10, reg_lit cs 12, reg_lit cs 21, reg_lit cs 19 with
    | [.ELit K], some i, some c, some s, some n =>
        let e := reg cs 11
        let cnt := n - i
        let lo := eaddz e (- (4 * n))
        let (lb, lk) := split_lit lo
        match xlo k e, xhi k e with
        | some el, some eh =>
            if (0 ≤ i && i < n && 4 * n ≤ el && eh < two64 && 0 ≤ c && 0 ≤ s
                && c + cnt * s < two64 && 0 ≤ K && K ≤ cnt && pc cs + 32 < two64
                && fresh_ok nx0 cs && kwritable_x k k lb lk (.ELit (4 * cnt))
                && off_image_x A k lb lk (.ELit (4 * cnt))) then
              let k1 := kn_havoc k lb lk (.ELit (4 * cnt))
              let kunk := if K < cnt then [.KUnk (SA lb lk) (.ELit (4 * (cnt - K)))] else []
              let sr := cs.a_ss.s_regs
              let sr' := sr_upd (sr_upd (sr_upd (sr_upd sr 10 (.ELit n)) 12 (.ELit (c + cnt * s)))
                                        14 (.ELit ((c + (cnt - 1) * s) / 16))) 15 lo
              some (with_ss cs (mk_ss (pc cs + 32) sr'
                (popfree_facts lb lk cnt c s K.toNat ++ kunk ++ k1) (nxt cs)))
            else none
        | _, _ => none
    | _, _, _, _, _ => none

/-- the range `rb+rk, rb+rk+ne` with a SYMBOLIC length lies inside ONE
    overlay-defined entry (Unk/Zero/Fill/Blob) of the knowledge — e.g. the
    havoc'ed read destination `p, p+n` of an n-byte class: every byte of it is
    readable, whatever n is. -/
def kn_readable_x (k : List kentry) (rb : expr) (rk : Int) (ne : expr) : Bool :=
  k.any (fun K =>
    match K with
    | .KUnk ⟨kb, kk⟩ len | .KZero ⟨kb, kk⟩ len | .KFill ⟨kb, kk⟩ len _
    | .KBlob ⟨kb, kk⟩ len _ => xinside k rb rk ne kb kk len
    | _ => false)

/-- pni_sniff_header(buf = a0, n = a1) at `x_sniff` (summary;
    the result is discarded by the fuzz target, so a0 is havoc'd like every
    caller-saved register): reads at most `buf, buf + min(n,8)`, the 16-byte
    jump table at `sniff_tab` (pristine image), for n >= 3 the shadow-base
    cell `sniff_cell` and ONE shadow byte at cell-value + buf/8 whose value
    must be 0 or in `min(nhi,8), 127`; writes only the ra slot `sp-8, sp`. -/
def summary_sniff_ref (A : atable) (segs : List Segment) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  if !(pc cs == A.x_sniff) then none
  else
    match ret_lit cs with
    | some ret =>
        let buf := reg cs 10
        let ne := reg cs 11
        let sp := reg cs 2
        let (bb, bk) := split_lit buf
        let (qb, qk) := split_lit (eaddz sp (-8))
        match xhi k ne, xhi k buf, xlo k sp, xhi k sp with
        | some nhi, some bhi, some splo, some sphi =>
            let m := min nhi 8
            if (bhi + 8 < two64 && 32 ≤ splo && sphi < two64 && A.sniff_tab + 16 + 8 ≤ splo
                && flat_x k qb qk (.ELit 8) && kwritable k k qb qk 8
                && flat_x k bb bk (.ELit 8)
                && ranges_apart_x k qb qk (.ELit 8) bb bk (.ELit 8)
                && ranges_apart_x k qb qk (.ELit 8) (.ELit 0) A.sniff_cell (.ELit 8)
                && (m == 0 || (flat_x k bb bk (.ELit m) && kn_readable segs k k bb bk m.toNat)
                    || kn_readable_x k bb bk ne)   -- `buf, buf+n` readable for the symbolic n itself
                && img_cov k A.sniff_tab (A.sniff_tab + 16)
                && (2 ≤ nhi ||
                    (3 ≤ ealign k buf && flat_x k (.ELit 0) A.sniff_cell (.ELit 8)
                     && (match xlo k buf with | some blo => 0 < blo | none => false)
                     && (match know_lookup segs k (.ELit 0) A.sniff_cell 8 false [] [] with
                         | .LHit esb [] _ =>
                             let sa := eadd esb (mkSrl k buf 3)
                             let (hb, hk) := split_lit sa
                             match xhi k esb with
                             | some ehi =>
                                 ehi + bhi / 8 + 1 < two64
                                 && flat_x k hb hk (.ELit 1)
                                 && ranges_apart_x k qb qk (.ELit 8) hb hk (.ELit 1)
                                 && (match know_lookup segs k hb hk 1 false [] [] with
                                     | .LHit v0 [] _ =>
                                         -- normalise the reloaded byte like the load path does
                                         -- (`EExt false 0 1 (EVar x)` with `x < 256` becomes `EVar x`)
                                         let v := extK k v0
                                         match erange k v with
                                         | some (lo, hi) =>
                                             (hi == 0) || (m ≤ lo && hi ≤ 127)
                                             -- symbolic partial granule `k >= n` itself
                                             || (hi ≤ 127 && lin_ge0 k [(v, (0 : Int))] [(ne, (0 : Int))])
                                         | none => false
                                     | _ => false)
                             | none => false
                         | _ => false)))) then
              after_call nx0 cs ret none (kn_havoc k qb qk (.ELit 8))
            else none
        | _, _, _, _ => none
    | none => none

/-- PERF: the same through the block context of the node's knowledge;
    `summary_sniff_eq`. -/
def summary_sniff (A : atable) (segs : List Segment) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  let bc := mkbc k       -- PERF: block context of the node's knowledge
  if !(pc cs == A.x_sniff) then none
  else
    match ret_lit cs with
    | some ret =>
        let buf := reg cs 10
        let ne := reg cs 11
        let sp := reg cs 2
        let (bb, bk) := split_lit buf
        let (qb, qk) := split_lit (eaddz sp (-8))
        match xhiB bc ne, xhiB bc buf, xloB bc sp, xhiB bc sp with
        | some nhi, some bhi, some splo, some sphi =>
            let m := min nhi 8
            if (bhi + 8 < two64 && 32 ≤ splo && sphi < two64 && A.sniff_tab + 16 + 8 ≤ splo
                && flat_xB bc qb qk (.ELit 8) && kwritableB bc k qb qk 8
                && flat_xB bc bb bk (.ELit 8)
                && ranges_apart_xB bc qb qk (.ELit 8) bb bk (.ELit 8)
                && ranges_apart_xB bc qb qk (.ELit 8) (.ELit 0) A.sniff_cell (.ELit 8)
                && (m == 0 || (flat_xB bc bb bk (.ELit m) && kn_readableB segs bc k bb bk m.toNat)
                    || kn_readable_x k bb bk ne)   -- `buf, buf+n` readable for the symbolic n itself
                && img_covB bc A.sniff_tab (A.sniff_tab + 16)
                && (2 ≤ nhi ||
                    (3 ≤ ealignB bc buf && flat_xB bc (.ELit 0) A.sniff_cell (.ELit 8)
                     && (match xloB bc buf with | some blo => 0 < blo | none => false)
                     && (match know_lookupB segs bc (.ELit 0) A.sniff_cell 8 false [] [] with
                         | .LHit esb [] _ =>
                             let sa := eadd esb (mkSrlB bc buf 3)
                             let (hb, hk) := split_lit sa
                             match xhiB bc esb with
                             | some ehi =>
                                 ehi + bhi / 8 + 1 < two64
                                 && flat_xB bc hb hk (.ELit 1)
                                 && ranges_apart_xB bc qb qk (.ELit 8) hb hk (.ELit 1)
                                 && (match know_lookupB segs bc hb hk 1 false [] [] with
                                     | .LHit v0 [] _ =>
                                         let v := extKB bc v0
                                         match erangeB bc v with
                                         | some (lo, hi) =>
                                             (hi == 0) || (m ≤ lo && hi ≤ 127)
                                             || (hi ≤ 127 && lin_ge0B bc [(v, (0 : Int))] [(ne, (0 : Int))])
                                         | none => false
                                     | _ => false)
                             | none => false
                         | _ => false)))) then
              after_call nx0 cs ret none (kn_havocB bc qb qk (.ELit 8))
            else none
        | _, _, _, _ => none
    | none => none

/-- `summary_sniff = summary_sniff_ref`. -/
theorem summary_sniff_eq (A : atable) (segs : List Segment) (nx0 : Nat) (cs : acs) :
    summary_sniff A segs nx0 cs = summary_sniff_ref A segs nx0 cs := by
  simp only [summary_sniff, summary_sniff_ref, ealignB_eqf, erangeB_eqf, extKB_eqf,
    flat_xB_eqf, img_covB_eqf, kn_havocB_eqf, kn_readableB_eqf, know_lookupB_eqf,
    kwritableB_eqf, lin_ge0B_eqf, mkSrlB_eqf, ranges_apart_xB_eqf, xhiB_eqf, xloB_eqf]
  try (with_unfolding_all exact rfl)

/-! Conventions for the INITIAL variables describing the argument block
    (AsanInit / the `SINV` instance must agree): sp / 32768. -/
def V_S1 : Nat := 0
/-- argc. -/
def V_ARGC : Nat := 1
/-- envc. -/
def V_ENVC : Nat := 2
/-- strlen(argv[0]). -/
def V_L0 : Nat := 3
/-- (string bytes + padding) / 8. -/
def V_W : Nat := 4
/-- initial break / 4096. -/
def V_BRK : Nat := 5
/-- (sp mod 32768) / 16, in `[0, 2047]`. -/
def V_S2 : Nat := 6
/-- strlen(argv[1]) when argc >= 2 (else 0). -/
def V_L1 : Nat := 7
/-- the launching uid (auxv AT_UID = AT_EUID value). -/
def V_UID : Nat := 8

/-- sp = 32768*s1 + 16*s2 (two variables so that the stack-shadow code's
    case split on sp mod 32 KiB is a PSplit on s2, F3). -/
def e_sp0 : expr := eadd (escale 32768 (.EVar V_S1)) (escale 16 (.EVar V_S2))

/-- envp = sp0 + 8*argc + 16 ; auxv = envp + 8*envc + 8 ; strings = auxv + 160
    (10 auxv pairs incl. AT_HWCAP). -/
def e_envp : expr := eadd e_sp0 (eadd (escale 8 (.EVar V_ARGC)) (.ELit 16))

/-- auxv. -/
def e_auxv : expr := eadd e_envp (eadd (escale 8 (.EVar V_ENVC)) (.ELit 8))

/-- the strings. -/
def e_str0 : expr := eaddz e_auxv 160

/-- argv[1]. -/
def e_str1 : expr := eadd e_str0 (eaddz (.EVar V_L0) 1)

/-- the AT_RANDOM block. -/
def e_atrandom : expr := eadd e_str0 (escale 8 (.EVar V_W))

/-- (e_atrandom - 184) / 8 as a linear form (the initial knowledge bounds it:
    the "sum fact" that bounds shadow addresses of the argument block). -/
def e_atr8 : expr :=
  eadd (eadd (escale 4096 (.EVar V_S1)) (escale 2 (.EVar V_S2)))
    (eadd (.EVar V_ARGC) (eadd (.EVar V_ENVC) (.EVar V_W)))

/-- the word at sp0+16 for EVERY argc: argv[1] (= argv[0] + L0 + 1) when
    argc >= 2, the argv NULL terminator when argc = 1 — spelled
    `[(1 <u argc) * e_str1]`; `XLayout` re-spells it once argc's class is known. -/
def e_argv1w : expr := .EMd .MUL (.EAlu .SLTU (.ELit 1) (.EVar V_ARGC)) e_str1

/-- musl's envp-counting loop `ld a0,0(s1); addi s1,s1,8; bnez a0` at
    `x_envscan`: s1 = envp on entry; exits at `x_envscan_k` with
    s1 = envp + 8*envc + 8, a0 = 0. -/
def node_envscan (A : atable) (cs : acs) : Option acs :=
  let k := kn cs
  if (pc cs == A.x_envscan && len_eqb k (reg cs 9) e_envp) then
    some (set_pc (set_reg (set_reg cs 9
              (eadd (reg cs 9) (eadd (escale 8 (.EVar V_ENVC)) (.ELit 8)))) 10 (.ELit 0))
            A.x_envscan_k)
  else none

/-- musl's program-name scan `lbu a3,-1(a1); beq a3,'/',store; bnez a3,loop`
    at `x_pnscan`: a1 = argv[0] + 1, a2 = 47, a0 = literal cell p (&__progname,
    writable); exits at `x_pnscan_k` with a3 = 0, a1 unknown (fresh), the cell
    holding an unknown pointer (havoc). -/
def node_pnscan (A : atable) (nx0 : Nat) (cs : acs) : Option acs :=
  let k := kn cs
  match reg_lit cs 10, reg_lit cs 12 with
  | some p, some 47 =>
      if (pc cs == A.x_pnscan && len_eqb k (reg cs 11) (eaddz e_str0 1)
          && kwritable k k (.ELit 0) p 8 && A.img_lo ≤ p && p + 8 ≤ A.img_hi
          && fresh_ok nx0 cs) then
        let v := nxt cs
        let k' := kn_havoc (kimg_cut k p 8) (.ELit 0) p (.ELit 8)
        let ss := cs.a_ss
        some (with_ss cs (mk_ss A.x_pnscan_k (sr_upd (sr_upd ss.s_regs 11 (.EVar v)) 13 (.ELit 0))
          k' (v + 1)))
      else none
  | _, _ => none

/-- `XLayout`: re-spell the conditional initial fact about the word at
    sp0+16 (`KWord (sp0+16) 8 e_argv1w`, see `e_argv1w`) once the class of
    argc is known: `XLayout [ELit 1]` (argc >= 2): the word is `e_str1`
    (argv[1]); `XLayout [ELit 0]` (argc <= 1): the word is 0 (argv's NULL).
    Pure consequence of the knowledge (no `SINV` needed). -/
def kw_argv1 (v : expr) : kentry := .KWord (SA e_sp0 16) 8 v

/-- `PX XLayout` re-spelling. -/
def node_layout (cs : acs) (args : List expr) : Option acs :=
  let k := kn cs
  if !(k.any (kentry_eqb (kw_argv1 e_argv1w))) then none
  else
    let k' := k.filter (fun K => !(kentry_eqb (kw_argv1 e_argv1w) K))
    match args with
    | [.ELit 1] =>
        match xlo k (.EVar V_ARGC) with
        | some lo => if 2 ≤ lo then some (set_kn cs (kw_argv1 e_str1 :: k')) else none
        | none => none
    | [.ELit 0] =>
        match xhi k (.EVar V_ARGC) with
        | some hi => if hi ≤ 1 then some (set_kn cs (kw_argv1 (.ELit 0) :: k')) else none
        | none => none
    | _ => none

/-! ### 8.8 hand-off: syntactic entailment of a stored state -/

/-- Syntactic entailment of the stored state `ch` by the current one. -/
def entails (cs : acs) (ch : acs) : Bool :=
  (pc cs == pc ch
   && (match ch.a_ss.s_log with | [] => true | _ => false)
   && list_eqb expr_eqb cs.a_ss.s_regs ch.a_ss.s_regs
   && (kn ch).all (fun K => (kn cs).any (kentry_eqb K))
   && list_eqb amap_eqb cs.a_maps ch.a_maps
   && list_eqb pair_eqb cs.a_vis ch.a_vis
   && list_eqb pair_eqb cs.a_ghost ch.a_ghost
   && expr_eqb cs.a_brk ch.a_brk
   && afd_eqb cs.a_fd ch.a_fd
   && (cs.a_tidset == ch.a_tidset)
   && cs.a_totsz ≤ ch.a_totsz && ch.a_ylo ≤ cs.a_ylo
   && cs.a_eager ≤ ch.a_eager && cs.a_abytes ≤ ch.a_abytes)

/-! ### 8.9 loops: template instantiation and havoc-aware entailment -/

/-- `esubst J e x`: x with `EVar J := e`, re-normalized bottom-up through the
    smart constructors (so that both sides of a loop-invariant comparison are
    in the same normal form). -/
def esubst (J : Nat) (e : expr) : expr → expr
  | x@(.ELit _) => x
  | x@(.EVar n) => if n == J then e else x
  | .EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | .EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | .EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | .EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | .EExt sx lo n a => .EExt sx lo n (esubst J e a)
  | x@(.EBlob _ _ _ _) => x

/-- addresses keep their literal offset (the semantics of a fact depends on
    the base/offset split through `estart`); `entails_h` compares addresses
    modulo re-splitting. -/
def asubst (J : Nat) (e : expr) (a : saddr) : saddr := SA (esubst J e a.a_base) a.a_off

/-- Substitute in a knowledge entry. -/
def ksubst (J : Nat) (e : expr) : kentry → kentry
  | .KWord a w v => .KWord (asubst J e a) w (esubst J e v)
  | .KZero a n => .KZero (asubst J e a) (esubst J e n)
  | .KBlob a n k => .KBlob (asubst J e a) (esubst J e n) k
  | .KImg lo hi => .KImg lo hi
  | .KAlign x m => .KAlign (esubst J e x) m
  | .KRange x lo hi => .KRange (esubst J e x) lo hi
  | .KWr a n => .KWr (asubst J e a) (esubst J e n)
  | .KDisj a1 n1 a2 n2 => .KDisj (asubst J e a1) (esubst J e n1) (asubst J e a2) (esubst J e n2)
  | .KFill a n c => .KFill (asubst J e a) (esubst J e n) c
  | .KUnk a n => .KUnk (asubst J e a) (esubst J e n)

/-- Substitute in a pair. -/
def psubst (J : Nat) (e : expr) (p : expr × expr) : expr × expr :=
  (esubst J e p.1, esubst J e p.2)

/-- Substitute in a ledger entry. -/
def msubst (J : Nat) (e : expr) (m : amap) : amap :=
  AM (esubst J e m.am_base) (esubst J e m.am_len) m.am_kind

/-- Substitute in the fd state. -/
def fsubst (J : Nat) (e : expr) : afd → afd
  | .FdFile k l o => .FdFile k (esubst J e l) (esubst J e o)
  | f => f

/-- the loop invariant template `inv` at iteration `e`. -/
def inst (inv : acs) (J : Nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (inv.a_ss.s_regs.map (esubst J e)) ((kn inv).map (ksubst J e)) (nxt inv))
      (inv.a_maps.map (msubst J e)) inv.a_totsz inv.a_ylo inv.a_eager
      (inv.a_vis.map (psubst J e)) (inv.a_ghost.map (psubst J e)) inv.a_abytes
      (esubst J e inv.a_brk) (fsubst J e inv.a_fd) inv.a_tidset

/-! #### 8.z VARIABLE RENAMING `PRename m` / `PCompact`

    nat-indexed partial map (no unary->binary conversion: `nth`). -/

/-- Set the `i`-th entry. -/
def nt_set (t : List (Option Nat)) (i : Nat) (d : Nat) : List (Option Nat) :=
  match i, t with
  | 0, [] => [some d]
  | 0, _ :: rest => some d :: rest
  | j + 1, [] => none :: nt_set [] j d
  | j + 1, x :: rest => x :: nt_set rest j d

/-- Read the `i`-th entry. -/
def nt_get (t : List (Option Nat)) (i : Nat) : Option Nat := t.getD i none

/-- `nt_get (nt_set t i d) j`. -/
theorem nt_get_set (t : List (Option Nat)) (i d : Nat) :
    ∀ j, nt_get (nt_set t i d) j = if j == i then some d else nt_get t j := by
  induction i generalizing t d with
  | zero =>
      intro j
      cases t with
      | nil => cases j <;> rfl
      | cons x rest => cases j <;> rfl
  | succ i ih =>
      intro j
      cases j with
      | zero =>
          cases t <;> rfl
      | succ j =>
          cases t with
          | nil =>
              have ih' : (nt_set [] i d).getD j none
                  = if (j == i) = true then some d
                    else ([] : List (Option Nat)).getD j none := by
                simpa only [nt_get] using ih [] d j
              simp only [nt_set, nt_get, List.getD_cons_succ, List.getD_nil]
              rw [ih']
              by_cases h : j = i
              · subst h; simp
              · simp [h, beq_iff_eq, Nat.succ.injEq]
          | cons x rest =>
              have ih' : (nt_set rest i d).getD j none
                  = if (j == i) = true then some d else rest.getD j none := by
                simpa only [nt_get] using ih rest d j
              simp only [nt_set, nt_get, List.getD_cons_succ]
              rw [ih']
              by_cases h : j = i
              · subst h; simp
              · simp [h, beq_iff_eq, Nat.succ.injEq]

/-- the forward table (src -> dst) of a pair list; `none` when a source repeats. -/
def mk_fwd : List (Nat × Nat) → Option (List (Option Nat))
  | [] => some []
  | (s, d) :: rest =>
      match mk_fwd rest with
      | some t => match nt_get t s with | none => some (nt_set t s d) | some _ => none
      | none => none

/-- the set of targets as a table (dst -> src); `none` when a target repeats. -/
def mk_bwd : List (Nat × Nat) → Option (List (Option Nat))
  | [] => some []
  | (s, d) :: rest =>
      match mk_bwd rest with
      | some t => match nt_get t d with | none => some (nt_set t d s) | some _ => none
      | none => none

/-- Rename the variables of an expression. -/
def erename (t : List (Option Nat)) : expr → expr
  | x@(.ELit _) => x
  | x@(.EVar v) => match nt_get t v with | some d => .EVar d | none => x
  | .EAlu op a b => .EAlu op (erename t a) (erename t b)
  | .EAluw op a b => .EAluw op (erename t a) (erename t b)
  | .EMd op a b => .EMd op (erename t a) (erename t b)
  | .EMdw op a b => .EMdw op (erename t a) (erename t b)
  | .EExt sx lo n a => .EExt sx lo n (erename t a)
  | x@(.EBlob _ _ _ _) => x

/-- Rename the variables of an address's base. -/
def arename (t : List (Option Nat)) (a : saddr) : saddr := SA (erename t a.a_base) a.a_off

/-- Rename the variables of a knowledge entry. -/
def krename (t : List (Option Nat)) : kentry → kentry
  | .KWord a w v => .KWord (arename t a) w (erename t v)
  | .KZero a n => .KZero (arename t a) (erename t n)
  | .KBlob a n k => .KBlob (arename t a) (erename t n) k
  | .KImg lo hi => .KImg lo hi
  | .KAlign x m => .KAlign (erename t x) m
  | .KRange x lo hi => .KRange (erename t x) lo hi
  | .KWr a n => .KWr (arename t a) (erename t n)
  | .KDisj a1 n1 a2 n2 => .KDisj (arename t a1) (erename t n1) (arename t a2) (erename t n2)
  | .KFill a n c => .KFill (arename t a) (erename t n) c
  | .KUnk a n => .KUnk (arename t a) (erename t n)

/-- Rename the variables of a pair. -/
def prename (t : List (Option Nat)) (p : expr × expr) : expr × expr :=
  (erename t p.1, erename t p.2)

/-- Rename the variables of a ledger entry. -/
def mrename (t : List (Option Nat)) (m : amap) : amap :=
  AM (erename t m.am_base) (erename t m.am_len) m.am_kind

/-- Rename the variables of the fd state. -/
def frename (t : List (Option Nat)) : afd → afd
  | .FdFile k l o => .FdFile k (erename t l) (erename t o)
  | f => f

/-- all variables of an expression satisfy `ok`. -/
def evars_all (ok : Nat → Bool) : expr → Bool
  | .ELit _ => true
  | .EVar v => ok v
  | .EAlu _ a b => evars_all ok a && evars_all ok b
  | .EAluw _ a b => evars_all ok a && evars_all ok b
  | .EMd _ a b => evars_all ok a && evars_all ok b
  | .EMdw _ a b => evars_all ok a && evars_all ok b
  | .EExt _ _ _ a => evars_all ok a
  | .EBlob _ _ _ _ => true

/-- all variables of a knowledge entry satisfy `ok`. -/
def kvars_all (ok : Nat → Bool) : kentry → Bool
  | .KWord a _ v => evars_all ok a.a_base && evars_all ok v
  | .KZero a n | .KBlob a n _ | .KWr a n | .KFill a n _ | .KUnk a n =>
      evars_all ok a.a_base && evars_all ok n
  | .KImg _ _ => true
  | .KAlign x _ | .KRange x _ _ => evars_all ok x
  | .KDisj a1 n1 a2 n2 =>
      evars_all ok a1.a_base && evars_all ok n1 && evars_all ok a2.a_base && evars_all ok n2

/-- all variables of the state satisfy `ok`. -/
def csvars_all (ok : Nat → Bool) (cs : acs) : Bool :=
  ((cs.a_ss.s_regs.all (evars_all ok) && (kn cs).all (kvars_all ok)
   && cs.a_maps.all (fun m => evars_all ok m.am_base && evars_all ok m.am_len)
   && cs.a_vis.all (fun p => evars_all ok p.1 && evars_all ok p.2)
   && cs.a_ghost.all (fun p => evars_all ok p.1 && evars_all ok p.2)
   && evars_all ok cs.a_brk
   && match cs.a_fd with | .FdFile _ l o => evars_all ok l && evars_all ok o | _ => true))

/-- largest variable index + 1 (0 if none). -/
def emaxv : expr → Nat → Nat
  | .ELit _, acc => acc
  | .EVar v, acc => max acc (v + 1)
  | .EAlu _ a b, acc => emaxv a (emaxv b acc)
  | .EAluw _ a b, acc => emaxv a (emaxv b acc)
  | .EMd _ a b, acc => emaxv a (emaxv b acc)
  | .EMdw _ a b, acc => emaxv a (emaxv b acc)
  | .EExt _ _ _ a, acc => emaxv a acc
  | .EBlob _ _ _ _, acc => acc

/-- The same for a knowledge entry. -/
def kmaxv : kentry → Nat → Nat
  | .KWord a _ v, acc => emaxv a.a_base (emaxv v acc)
  | .KZero a n, acc | .KBlob a n _, acc | .KWr a n, acc | .KFill a n _, acc
  | .KUnk a n, acc => emaxv a.a_base (emaxv n acc)
  | .KImg _ _, acc => acc
  | .KAlign x _, acc | .KRange x _ _, acc => emaxv x acc
  | .KDisj a1 n1 a2 n2, acc => emaxv a1.a_base (emaxv n1 (emaxv a2.a_base (emaxv n2 acc)))

/-- The same for the state. -/
def csmaxv (cs : acs) : Nat :=
  let acc := cs.a_ss.s_regs.foldr emaxv 0
  let acc := (kn cs).foldr kmaxv acc
  let acc := cs.a_maps.foldr (fun m acc => emaxv m.am_base (emaxv m.am_len acc)) acc
  let acc := cs.a_vis.foldr (fun p acc => emaxv p.1 (emaxv p.2 acc)) acc
  let acc := cs.a_ghost.foldr (fun p acc => emaxv p.1 (emaxv p.2 acc)) acc
  let acc := match cs.a_fd with | .FdFile _ l o => emaxv l (emaxv o acc) | _ => acc
  emaxv cs.a_brk acc

/-- Rename every variable of the state. -/
def rename_cs (t : List (Option Nat)) (cs : acs) (nx : Nat) : acs :=
  ACS (mk_ss (pc cs) (cs.a_ss.s_regs.map (erename t)) ((kn cs).map (krename t)) nx)
      (cs.a_maps.map (mrename t)) cs.a_totsz cs.a_ylo cs.a_eager
      (cs.a_vis.map (prename t)) (cs.a_ghost.map (prename t)) cs.a_abytes
      (erename t cs.a_brk) (frename t cs.a_fd) cs.a_tidset

/-- `PRename m` at GC bound `gb` (= nx0 outside loop bodies): sources and
    targets at or above `gb`, sources distinct, targets distinct, and a target
    that occurs in the state must itself be renamed away (simultaneous
    renaming); then the state is rewritten and `nxt` := max gb (1 + largest
    variable of the renamed state). -/
def node_rename (gb : Nat) (cs : acs) (m : List (Nat × Nat)) : Option acs :=
  if m.all (fun p => gb ≤ p.1 && gb ≤ p.2) then
    match mk_fwd m, mk_bwd m with
    | some fw, some bw =>
        let ok (v : Nat) : Bool :=
          match nt_get fw v with
          | some _ => true
          | none => match nt_get bw v with | some _ => false | none => true
        if (csvars_all ok cs && (match cs.a_ss.s_log with | [] => true | _ => false)) then
          let cs1 := rename_cs fw cs 0
          some (with_ss cs1 (mk_ss (pc cs1) cs1.a_ss.s_regs (kn cs1) (max gb (csmaxv cs1))))
        else none
    | _, _ => none
  else none

/-- Set the `i`-th entry of a `Bool` table. -/
def bt_set (t : List Bool) (i : Nat) : List Bool :=
  match i, t with
  | 0, [] => [true]
  | 0, _ :: rest => true :: rest
  | j + 1, [] => false :: bt_set [] j
  | j + 1, x :: rest => x :: bt_set rest j

/-- Read the `i`-th entry of a `Bool` table. -/
def bt_get (t : List Bool) (i : Nat) : Bool := t.getD i false

/-- first-occurrence list (reversed) + seen table. -/
def evars_fo (gb : Nat) : expr → List Nat × List Bool → List Nat × List Bool
  | .ELit _, acc => acc
  | .EVar v, acc =>
      if v < gb then acc
      else if bt_get acc.2 v then acc
      else (v :: acc.1, bt_set acc.2 v)
  | .EAlu _ a b, acc => evars_fo gb b (evars_fo gb a acc)
  | .EAluw _ a b, acc => evars_fo gb b (evars_fo gb a acc)
  | .EMd _ a b, acc => evars_fo gb b (evars_fo gb a acc)
  | .EMdw _ a b, acc => evars_fo gb b (evars_fo gb a acc)
  | .EExt _ _ _ a, acc => evars_fo gb a acc
  | .EBlob _ _ _ _, acc => acc

/-- The same for a knowledge entry. -/
def kvars_fo (gb : Nat) : kentry → List Nat × List Bool → List Nat × List Bool
  | .KWord a _ v, acc => evars_fo gb v (evars_fo gb a.a_base acc)
  | .KZero a n, acc | .KBlob a n _, acc | .KWr a n, acc | .KFill a n _, acc
  | .KUnk a n, acc => evars_fo gb n (evars_fo gb a.a_base acc)
  | .KImg _ _, acc => acc
  | .KAlign x _, acc | .KRange x _ _, acc => evars_fo gb x acc
  | .KDisj a1 n1 a2 n2, acc =>
      evars_fo gb n2 (evars_fo gb a2.a_base (evars_fo gb n1 (evars_fo gb a1.a_base acc)))

/-- The first-occurrence list of the state's variables at or above `gb`. -/
def csvars_fo (gb : Nat) (cs : acs) : List Nat :=
  let acc := cs.a_ss.s_regs.foldl (fun acc e => evars_fo gb e acc) ([], [])
  let acc := (kn cs).foldl (fun acc K => kvars_fo gb K acc) acc
  let acc := cs.a_maps.foldl (fun acc m =>
    evars_fo gb m.am_len (evars_fo gb m.am_base acc)) acc
  let acc := cs.a_vis.foldl (fun acc p =>
    evars_fo gb p.2 (evars_fo gb p.1 acc)) acc
  let acc := cs.a_ghost.foldl (fun acc p =>
    evars_fo gb p.2 (evars_fo gb p.1 acc)) acc
  let acc := match cs.a_fd with
    | .FdFile _ l o => evars_fo gb o (evars_fo gb l acc)
    | _ => acc
  let acc := evars_fo gb cs.a_brk acc
  acc.1.reverse

/-- Number the list from `i`. -/
def number_from (i : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | v :: rest => (v, i) :: number_from (i + 1) rest

/-- The canonical dense renaming map. -/
def compact_map (gb : Nat) (cs : acs) : List (Nat × Nat) :=
  number_from gb (csvars_fo gb cs)

/-- `PCompact`. -/
def node_compact (gb : Nat) (cs : acs) : Option acs := node_rename gb cs (compact_map gb cs)

/-- havoc-aware entailment: registers of the template `ch` that are a bare
    havoc variable `EVar v`, `lo <= v < hi`, match any register of `cs` (each
    such v at most once); everything else as `entails`. -/
def regs_match_h (lo hi : Nat) (seen : List Nat) : List expr → List expr → Bool
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | .EVar v =>
          if (lo ≤ v && v < hi) then
            (!(seen.any (fun x => v == x)) && regs_match_h lo hi (v :: seen) rs' ts')
          else (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')
      | _ => (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')
  | _, _ => false

/-- the same address, possibly split differently: equal full addresses (as
    normal forms) — the caller also checks the template side flat. -/
def saddr_eqb_h (x y : saddr) : Bool :=
  saddr_eqb x y || expr_eqb (eaddz x.a_base x.a_off) (eaddz y.a_base y.a_off)

/-- COVERAGE (for template `KUnk` entries): byte `b+i` is
    overlay-DEFINED if it lies inside a KWord (caller: off the image) or a
    literal-extent KZero/KFill/KBlob/KUnk entry with the same base expression;
    `cover1` returns the end offset of such an entry, `cover_x` walks `i, stop`. -/
def cover1 (k : List kentry) (b : expr) (i : Int) : Option Int :=
  match k with
  | [] => none
  | K :: rest =>
      let hit := match K with
        | .KWord ⟨kb, kk⟩ w _ =>
            if (expr_eqb b kb && kk ≤ i && i < kk + (w : Int)) then some (kk + (w : Int)) else none
        | .KZero ⟨kb, kk⟩ (.ELit l) | .KFill ⟨kb, kk⟩ (.ELit l) _
        | .KBlob ⟨kb, kk⟩ (.ELit l) _ | .KUnk ⟨kb, kk⟩ (.ELit l) =>
            if (expr_eqb b kb && 0 ≤ l && l < two64 && kk ≤ i && i < kk + l) then some (kk + l) else none
        | _ => none
      match hit with
      | some e => some e
      | none => cover1 rest b i

/-- Walk `i, stop` through `cover1`. -/
def cover_x (fuel : Nat) (k : List kentry) (b : expr) (i : Int) (stop : Int) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
      if stop ≤ i then true
      else
        match cover1 k b i with
        | some e => if i < e then cover_x f k b e stop else false
        | none => false

/-- a template entry `KUnk (SA b o) (ELit n)` holds if the state's knowledge
    covers `b+o, +n` off the image (n literal, up to 2^40; the walk needs at
    most one step per knowledge entry). -/
def kunk_covered (A : atable) (k : List kentry) (K : kentry) : Bool :=
  match K with
  | .KUnk ⟨b, o⟩ (.ELit n) =>
      (0 < n && n ≤ zpow 2 40 && A.img_lo ≤ A.img_hi && flat_x k b o (.ELit n)
       && off_image_x A k b o (.ELit n) && cover_x (k.length + 1) k b o (o + n))
  | _ => false

/-- Boolean equality of template/state entries modulo re-splitting. -/
def kentry_eqb_h (x y : kentry) : Bool :=
  kentry_eqb x y
  || match x, y with
     | .KWord a w v, .KWord a' w' v' => saddr_eqb_h a a' && (w == w') && expr_eqb v v'
     | .KZero a n, .KZero a' n' => saddr_eqb_h a a' && expr_eqb n n'
     | .KBlob a n k, .KBlob a' n' k' => saddr_eqb_h a a' && expr_eqb n n' && (k == k')
     | .KWr a n, .KWr a' n' => saddr_eqb_h a a' && expr_eqb n n'
     | .KFill a n c, .KFill a' n' c' => saddr_eqb_h a a' && expr_eqb n n' && (c == c')
     | .KUnk a n, .KUnk a' n' => saddr_eqb_h a a' && expr_eqb n n'
     | _, _ => false

/-- flatness of a template memory entry, decided from the state's knowledge. -/
def kflat_h (k : List kentry) : kentry → Bool
  | .KWord ⟨b, o⟩ w _ => flat_x k b o (.ELit (w : Int))
  | .KZero ⟨b, o⟩ n | .KBlob ⟨b, o⟩ n _ | .KWr ⟨b, o⟩ n | .KFill ⟨b, o⟩ n _
  | .KUnk ⟨b, o⟩ n => flat_x k b o n
  | _ => true

/-- a template `KImg lo hi` also holds if the state has a LARGER
    undefined-overlay range around it (arms that split the image entry at
    different cells meet on the common sub-ranges). -/
def kimg_sub_covered (k : List kentry) (K : kentry) : Bool :=
  match K with
  | .KImg lo hi =>
      k.any (fun X => match X with | .KImg lo' hi' => lo' ≤ lo && hi ≤ hi' | _ => false)
  | _ => false

/-- (nested `if`s, not `||`: under cbv evaluation the cheap exact test must
    short-circuit the `xlo`/`xhi`-based ones — a `PDiamond` cost). -/
def kn_incl1_h (A : atable) (k : List kentry) (K : kentry) : Bool :=
  if k.any (fun X => kentry_eqb X K) then true
  else if (if kflat_h k K then k.any (fun X => kentry_eqb_h X K) else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered A k K

/-- Is every template entry included in the state's knowledge? -/
def kn_incl_h (A : atable) (k : List kentry) (tk : List kentry) : Bool := tk.all (kn_incl1_h A k)

/-- Havoc-aware entailment. -/
def entails_h (A : atable) (lo hi : Nat) (cs : acs) (ch : acs) : Bool :=
  (pc cs == pc ch
   && (match ch.a_ss.s_log with | [] => true | _ => false)
   && (match ch.a_ss.s_resv with | none => true | _ => false)
   && regs_match_h lo hi [] cs.a_ss.s_regs ch.a_ss.s_regs
   && kn_incl_h A (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo ch.a_maps && pairs_vars_lt lo ch.a_vis
   && pairs_vars_lt lo ch.a_ghost
   && expr_vars_lt lo ch.a_brk && fd_vars_lt lo ch.a_fd
   && list_eqb amap_eqb cs.a_maps ch.a_maps
   && list_eqb pair_eqb cs.a_vis ch.a_vis
   && list_eqb pair_eqb cs.a_ghost ch.a_ghost
   && expr_eqb cs.a_brk ch.a_brk
   && afd_eqb cs.a_fd ch.a_fd
   && (cs.a_tidset == ch.a_tidset)
   && cs.a_totsz ≤ ch.a_totsz && ch.a_ylo ≤ cs.a_ylo
   && cs.a_eager ≤ ch.a_eager && cs.a_abytes ≤ ch.a_abytes)

/-- the context passed down into a loop body / into the arms of a `PVia`:
    `LC`: head pc, the next-iteration template, the havoc variable range;
    `JC`: join id, the join state, the continuation's shape, the
    protected variable bound (the counter at the `PVia`) and the start of the
    join state's register-havoc range.  `lc_bnd` = the GC / rename bound
    inside (variables below it are frozen). -/
inductive loopctx : Type
  | LC (lc_head : Int) (lc_next : acs) (lc_lo lc_hi : Nat)
  | JC (jc_id : Nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : Nat)
  deriving DecidableEq, Repr

/-- The GC / rename bound inside. -/
def lc_bnd : loopctx → Nat
  | .LC _ _ _ hi => hi
  | .JC _ _ _ b _ => b

/-- well-formedness of `PLoop J N inv` at `cs0`: returns Nhi. -/
def loop_ok (nx0 : Nat) (cs0 : acs) (J : Nat) (N : expr) (inv : acs) : Option Int :=
  let lo := J + 1
  let hi := nxt inv
  if (fresh_ok nx0 cs0 && nxt cs0 ≤ J && J < hi && fresh_ok nx0 inv
      && expr_vars_lt (nxt cs0) N
      && (match inv.a_ss.s_log with | [] => true | _ => false)
      && inv.a_ss.s_regs.length == 32
      && kn_vars_lt lo (kn inv) && maps_vars_lt lo inv.a_maps && pairs_vars_lt lo inv.a_vis
      && pairs_vars_lt lo inv.a_ghost
      && expr_vars_lt lo inv.a_brk && fd_vars_lt lo inv.a_fd
      && inv.a_ss.s_regs.all (fun r => match r with | .EVar _ => true | _ => expr_vars_lt lo r)
      && regs_match_h lo hi [] inv.a_ss.s_regs inv.a_ss.s_regs) then
    match xhi (kn cs0) N with
    | some nhi => if nhi < two64 then some nhi else none
    | none => none
  else none

/-- the body's start state: the template at `EVar J` plus the iteration bounds. -/
def loop_body_state (J : Nat) (N : expr) (nhi : Int) (inv : acs) : acs :=
  add_kn inv [.KRange (.EVar J) 0 (nhi - 1), .KRange (esub N (.EVar J)) 1 nhi]

/-! #### 8.10 diamonds: an undecidable conditional branch whose two arms re-join

    `PDiamond joinpc rs`: the instruction at `pc` is a conditional branch the
    executor cannot decide.  The checker case-splits on the executor's own
    PROBE expression of the condition (`AX2.cond_probe`, value 0 or 1; with the
    fact `KRange probe v v` in the knowledge the executor's `enum_branch`
    decides the branch), runs BOTH arms as blocks to `joinpc`, and re-joins:
    every register whose expressions differ between the two end states (plus
    `rs`) becomes a fresh variable, the knowledge is the common part, and both
    end states must entail the joined state (`entails_h`, the loop machinery's
    havoc-aware entailment).  No new trust: soundness is split + run + entail. -/

/-- The executor's probe of the branch at `pc`. -/
def branch_probe (IT : itab) (cs : acs) : Option expr :=
  match itab_lookup IT (pc cs) with
  | some (.branch c rs1 rs2 _) =>
      some (cond_probe c (sr_get cs.a_ss.s_regs rs1) (sr_get cs.a_ss.s_regs rs2)).1
  | _ => none

/-- indices (from `i`) at which the two register files differ syntactically. -/
def diff_regs (i : Nat) : List expr → List expr → List Nat
  | a :: ra', b :: rb' => if expr_eqb a b then diff_regs (i + 1) ra' rb' else i :: diff_regs (i + 1) ra' rb'
  | _, _ => []

/-- the joined state after the two arm end states `ca` / `cb` (both at
    `joinpc`); fresh variables from `max nx (nxt ca) (nxt cb)`, `nx` = the
    counter at the branch. -/
def node_diamond_join (A : atable) (nx0 : Nat) (nx : Nat) (joinpc : Int) (rs : List Nat)
    (ca cb : acs) : Option acs :=
  let hv := (diff_regs 0 ca.a_ss.s_regs cb.a_ss.s_regs ++ rs).eraseDups
  let v0 := max nx (max (nxt ca) (nxt cb))
  let hi := v0 + hv.length
  let regsJ := sr_fresh ca.a_ss.s_regs hv v0
  let knJ := (kn ca).filter (fun K => (kn cb).any (fun X => kentry_eqb X K))
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi)
  if (pc ca == joinpc && pc cb == joinpc
      && hv.all (fun r => 0 < r && r < 32)
      && regsJ.length == 32
      && nx0 ≤ v0
      && entails_h A v0 hi ca csJ && entails_h A v0 hi cb csJ) then
    some csJ
  else none

/-! #### 8.11 inline joins `PVia`/`PMerge`, cell abstraction, word havoc -/

/-- `PVia j js lo karms k` at `cs`: well-formedness of the offline join state
    `js`: empty log, 32 registers, and the variable discipline
    nx0 <= nxt cs <= lo <= nxt js (variables below `nxt cs` are frozen inside
    `karms`; `js`'s non-havoc parts mention only variables below `lo`; its
    register-havoc slots are `EVar v`, lo <= v < nxt js). -/
def via_ok (nx0 : Nat) (cs js : acs) (lo : Nat) : Bool :=
  ((match js.a_ss.s_log with | [] => true | _ => false)
   && js.a_ss.s_regs.length == 32
   && nx0 ≤ nxt cs && nxt cs ≤ lo && lo ≤ nxt js)

/-- `PAbstractCell b n`: the OFF-IMAGE byte range `b, b+n` (n literal), covered
    by the knowledge (Word/Zero/Fill/Blob/Unk entries, `kunk_covered`), becomes
    ONE `KUnk` entry: every other fact about it is cut out; later loads there
    yield fresh variables.  Pure weakening. -/
def node_abstractcell (A : atable) (cs : acs) (b : expr) (n : Int) : Option acs :=
  let (bb, bo) := split_lit b
  let K := .KUnk (SA bb bo) (.ELit n)
  if kunk_covered A (kn cs) K then
    some (set_kn cs (K :: kn_cutout (kn cs) bb bo (.ELit n)))
  else none

/-- `PRespell r e`: register `r` (1..31) is re-spelled as the expression `e`
    (over variables below the counter) when the knowledge proves the two EQUAL
    as 64-bit values (`respell_ok`: `AX2.decide_branch BC_EQ` = literals /
    syntactic / singleton intervals / exact linear arithmetic both ways, or
    the interval of `reg r - e` is `0,0`).  Pure: the concrete registers are
    unchanged.  Use it to give the arms of a `PVia` one common spelling of a
    live register before `PMerge` (e.g. calls = 1 + XCM * ((CFGX+32767)>>15)). -/
def respell_ok (k : List kentry) (a e : expr) : Bool :=
  match decide_branch k .EQ a e with
  | some true => true
  | _ => -- the difference is 0 modulo 2^64 by interval arithmetic (no no-wrap evidence needed)
    match erange k (mkAlu .SUB a e) with
    | some (lo, hi) => lo == 0 && hi == 0
    | none => false

/-- `PRespell`. -/
def node_respell (cs : acs) (r : Nat) (e : expr) : Option acs :=
  if (0 < r && r < 32 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e) then
    some (set_reg cs r e)
  else none

/-- `PHavocWords bs`: for the i-th listed address, the value of the FIRST
    `KWord` fact at exactly that (split) address becomes the fresh variable
    `EVar (nxt + i)`; any further `KWord` fact at the same address is dropped.
    (valuation extension; the state must be closed below its counter) -/
def sa_of (b : expr) : saddr :=
  let (bb, bo) := split_lit b
  SA bb bo

/-- Replace the first `KWord` value at `a` by `EVar x`. -/
def hw_apply (k : List kentry) (a : saddr) (x : Nat) (found : Bool) : List kentry :=
  match k with
  | [] => []
  | .KWord a' w v :: r =>
      if saddr_eqb a' a then
        (if found then hw_apply r a x true else .KWord a' w (.EVar x) :: hw_apply r a x true)
      else .KWord a' w v :: hw_apply r a x found
  | K :: r => K :: hw_apply r a x found

/-- the replaced value (for the soundness proof's valuation): the first KWord
    value at `a`, else 0. -/
def hw_val (k : List kentry) (a : saddr) : expr :=
  match k with
  | [] => .ELit 0
  | .KWord a' _ v :: r => if saddr_eqb a' a then v else hw_val r a
  | _ :: r => hw_val r a

/-- Walk the listed addresses. -/
def hw_go (k : List kentry) : List expr → Nat → List kentry
  | [], _ => k
  | b :: r, x => hw_go (hw_apply k (sa_of b) x false) r (x + 1)

/-- `PHavocWords`. -/
def node_havocwords (nx0 : Nat) (cs : acs) (bs : List expr) : Option acs :=
  if fresh_ok nx0 cs then
    let ss := cs.a_ss
    some (with_ss cs (mk_ss ss.s_pc ss.s_regs (hw_go ss.s_know bs ss.s_next)
      (ss.s_next + bs.length)))
  else none

/-! ### 9. The checker (the part that lives in the `WithSegs` context) -/

/-- The resume stops of a block run. -/
def STOPS (A : atable) : List Int :=
  [A.x_imemset, A.x_imemcpy, A.x_memset, A.x_memcpy, A.x_memiszero, A.x_envscan, A.x_pnscan]
    ++ A.stops_more

/-- A PARTIAL instruction table over several code ranges `(lo, n)` (n words
    from lo each): decoding all of .text costs ~17 s of native_compute per
    certificate file; a table restricted to the ranges a plan visits costs a
    fraction and is just as sound (`AsanPlanSound.mk_itab_ranges_sound`: a
    missing entry only makes the executor stop). -/
def mk_itab_ranges_acc (segs : List Segment) : List (Int × Nat) → itab → itab
  | [], t => t
  | (lo, n) :: rs', t => mk_itab_ranges_acc segs rs' (mk_itab_fuel segs n lo t)

/-- The partial instruction table. -/
def mk_itab_ranges (segs : List Segment) (rs : List (Int × Nat)) : itab :=
  mk_itab_ranges_acc segs rs .PTLeaf

end WithSegs

/-! ## 9b. The initial checker state of an image (at `a_entry A`) -/

/-- Brk ASLR window `State.brk_aslr_max` and the initial-variable count. -/
def BRK_ASLR : Int := 0x80000000

/-- The initial-variable count (includes `V_UID`). -/
def NX0 : Nat := 9

/-- the 16 AT_RANDOM bytes are a per-run kernel draw (`ed_random` of
    `Run.en_draw`, a `StackLayout.EntryDraw`).  The FAITHFUL initial knowledge
    reads them as byte string `K_RND`, bound to `at_random_bytes rdraw` in the
    initial valuation `AsanInit.E0`: a load inside the block denotes
    `EBlob _ K_RND off n`, the idiom the argv strings (byte strings 1, 2) and
    the FILE contents (0) use.  `K_RND` is reserved — a plan must never rebind
    it (the AT_RANDOM auxv type, 25, as the mnemonic; far from the small
    indices plans allocate). -/
def K_RND : Nat := 25

/-- (split forms as constants: definitions over them must not block on the
    smart constructors' normalization when unfolded in proofs). -/
def e_auxb : expr × Int := split_lit e_auxv

/-- The split form of `e_atrandom`. -/
def e_atrb : expr × Int := split_lit e_atrandom

/-- The two auxv words of pair `i`. -/
def auxw (i : Int) (ty : Int) (v : expr) : List kentry :=
  [.KWord (SA e_auxb.1 (e_auxb.2 + 16 * i)) 8 (.ELit ty),
   .KWord (SA e_auxb.1 (e_auxb.2 + 16 * i + 8)) 8 v]

/-- What the checker knows at `_start` (justified by `AsanInit.init_cs_ok`):
    ranges of the initial variables and the sum facts (most specific first),
    the zero-filled writable 8 MiB below sp, argc / argv[0] / the sp0+16 word,
    the 20 auxv words (AT_UID/AT_EUID = EVar V_UID; AT_HWCAP = the hwcap word),
    the AT_RANDOM block (`atr`: the faithful byte-string entry, or the zero
    entry), the image hull with no overlay and its writable window. -/
def init_kn_with (atr : kentry) (A : atable) : List kentry :=
  [.KRange (.EVar V_S1) 0xFFFF0000 0xFFFFFFFF, .KRange (.EVar V_S2) 0 2047,
   .KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000,
   .KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE9,
   .KRange e_sp0 0x7fff80000000 0x7fffffffff40,
   .KRange (eadd (escale 4096 (.EVar V_S1)) (escale 2 (.EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8,
   .KRange (.EVar V_ARGC) 1 1024, .KRange (.EVar V_ENVC) 0 256,
   .KRange (.EVar V_L0) 0 131071, .KRange (.EVar V_L1) 0 131071,
   .KRange (.EVar V_UID) 0 0xFFFFFFFE,
   .KRange (.EVar V_W) 0 280000,
   .KRange (.EVar V_BRK) (A.img_hi / 4096) ((A.img_hi + BRK_ASLR) / 4096),
   .KWr (SA e_sp0 (-8388608)) (.ELit 8388608),
   .KZero (SA e_sp0 (-8388608)) (.ELit 8388608),
   .KWord (SA e_sp0 0) 8 (.EVar V_ARGC), .KWord (SA e_sp0 8) 8 e_str0, kw_argv1 e_argv1w]
  -- pair 3 is (AT_HWCAP = 16, the run's hwcap word) — not claimed (no plan
  -- variable denotes it); pairs 4..9 follow
  ++ auxw 0 3 (.ELit A.ph_addr_z) ++ auxw 1 4 (.ELit A.ph_ent_z)
  ++ auxw 2 5 (.ELit A.ph_num_z) ++ auxw 4 6 (.ELit 4096)
  ++ auxw 5 11 (.EVar V_UID) ++ auxw 6 12 (.EVar V_UID) ++ auxw 7 23 (.ELit 0)
  ++ auxw 8 25 e_atrandom ++ auxw 9 0 (.ELit 0)
  ++ [atr,
      .KImg A.img_lo A.img_hi,
      .KWr (SA (.ELit 0) A.rw_lo) (.ELit A.rw_len)]

/-- the AT_RANDOM entry, faithful (the draw, as byte string `K_RND`). -/
def atr_entry : kentry := .KBlob (SA e_atrb.1 e_atrb.2) (.ELit 16) K_RND

/-- the AT_RANDOM entry, zero (FALSE on every real run; sound only under
    `AsanCeil.zero_random_draw`). -/
def atr_entry_zero : kentry := .KZero (SA e_atrb.1 e_atrb.2) (.ELit 16)

/-- THE DEFAULT: what new plans start from (justified by `AsanInit.init_cs_ok`). -/
def init_kn (A : atable) : List kentry := init_kn_with atr_entry A

/-- ZERO DRAW: for certificates and hand-off states built on the zero entry
    (justified by `AsanInit.init_cs_ok_zero`, under the hypothesis that the
    draw is zero). -/
def init_kn_zero (A : atable) : List kentry := init_kn_with atr_entry_zero A

/-- The initial register file. -/
def init_regs : List expr := sr_upd (List.replicate 32 (.ELit 0)) 2 e_sp0

/-- visible application ranges at start: the image hull and the whole stack side. -/
def init_vis (A : atable) : List (expr × expr) :=
  [(.ELit A.img_lo, .ELit (A.img_hi - A.img_lo)), (.ELit CEIL, .ELit (zpow 2 47 - CEIL))]

/-- The initial checker state, from a given initial knowledge. -/
def init_acs_of_with (kn0 : List kentry) (A : atable) : acs :=
  ACS (mk_ss A.a_entry init_regs kn0 NX0) [] (A.img_hi - A.img_lo) MBASE_MIN 0 (init_vis A) []
      (vis_cost (A.img_hi - A.img_lo) + vis_cost (zpow 2 47 - CEIL))
      (escale 4096 (.EVar V_BRK)) .FdStd false

/-- THE DEFAULT initial checker state. -/
def init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A

/-- The initial checker state under the zero draw. -/
def init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A

/-! ## 10. Address tables -/

/-- target_fuzz_sniff_header_asan (image
    Tgt_fuzz_sniff_header_asan): segments r 0x10000+0x3b000, rx 0x4b000+0xf7000,
    rw 0x142000+0x3000, rw 0x145000+0x52c000 (contiguous hull `0x10000, 0x671000`),
    entry 0x4ba64.  Routine addresses located by matching the routines' code words in
    a disassembly of the image: compiler-rt
    internal_memset 0xe1ea4 / internal_memcpy 0xe1e28 / mem_is_zero 0xe2508
    (their address +4), musl memset 0x116934 / memcpy 0x116530 (their address -0xf18), __init_libc
    env-scan loop 0x10d5e4 (exit 0x10d5f0), progname scan 0x10d6a8 (exit 0x10d6b4). -/
def ASAN : atable where
  img_lo := 0x10000
  img_hi := 0x671000
  n_res := 4
  shadow_off := 0x7fff8000
  a_entry := 0x4ba64
  rw_lo := 0x142000
  rw_len := 0x52f000
  ph_addr_z := 0x10040
  ph_ent_z := 56
  ph_num_z := 11
  x_imemset := 0xe1ea4
  x_imemcpy := 0xe1e28
  x_memset := 0x116934
  x_memcpy := 0x116530
  x_memiszero := 0xe2508
  x_istrncpy := 0xe23b8
  x_sealed := 0x1205f
  x_popfree := 0x52a70
  x_sniff := 0x1414dc
  sniff_tab := 0x24f40
  sniff_cell := 0x14bf00
  x_envscan := 0x10d5e4
  x_envscan_k := 0x10d5f0
  x_pnscan := 0x10d6a8
  x_pnscan_k := 0x10d6b4
  stops_more := [0x506e4, 0x51d08, 0xddd88, 0xee070, 0xee200]  -- the sealed self-loops

/-- the decoded-instruction table range of the asan text. -/
def ASAN_TEXT_LO : Int := 0x4ba64

/-- Its length in words. -/
def ASAN_TEXT_N : Nat := 252263

/-- The asan initial state. -/
def asan_init : acs := init_acs_of ASAN

/-- target_fuzz_sniff_header_both: code = asan - 0x10
    for everything below pni_sniff_header (0x1414dc); same segment layout
    (not confirmed; data delta assumed 0). -/
def BOTH : atable where
  img_lo := 0x10000
  img_hi := 0x671000
  n_res := 4
  shadow_off := 0x7fff8000
  a_entry := 0x4ba54
  rw_lo := 0x142000
  rw_len := 0x52f000
  ph_addr_z := 0x10040
  ph_ent_z := 56
  ph_num_z := 11
  x_imemset := 0xe1e94
  x_imemcpy := 0xe1e18
  x_memset := 0x116924
  x_memcpy := 0x116520
  x_memiszero := 0xe24f8
  x_istrncpy := 0xe23a8
  x_sealed := 0x1205f
  x_popfree := 0x52a60
  x_sniff := 0x1414cc
  sniff_tab := 0x24f40
  sniff_cell := 0x14bf80   -- both has no jump table; tab = placeholder
  x_envscan := 0x10d5d4
  x_envscan_k := 0x10d5e0
  x_pnscan := 0x10d698
  x_pnscan_k := 0x10d6a4
  stops_more := [0x506d4, 0x51cf8, 0xddd78, 0xee060, 0xee1f0]

/-- the decoded-instruction table range of the both text. -/
def BOTH_TEXT_LO : Int := 0x4ba54

/-- Its length in words. -/
def BOTH_TEXT_N : Nat := 252267

/-- The both initial state. -/
def both_init : acs := init_acs_of BOTH

/-- `forallb` over the walk: the accumulator can be split off. -/
theorem forallb_expr_vars (P : Nat → Bool) (e : expr) :
    ∀ acc, (expr_vars e acc).all P = ((expr_vars e []).all P && acc.all P) := by
  induction e with
  | ELit z => intro acc; simp [expr_vars]
  | EVar n =>
      intro acc
      by_cases h : acc.any (fun x => n == x) = true
      · have hn : n ∈ acc := by
          obtain ⟨a, ha, hb⟩ := List.any_eq_true.mp h
          rw [beq_iff_eq] at hb
          subst hb
          exact ha
        by_cases hP : acc.all P = true
        · have hp : P n = true := List.all_eq_true.mp hP n hn
          simp [expr_vars, h, hP, hp]
        · simp [expr_vars, h, hP]
      · simp [expr_vars, h]
  | EAlu op a b iha ihb =>
      intro acc
      simp only [expr_vars]
      rw [iha (expr_vars b acc), ihb acc, iha (expr_vars b []), Bool.and_assoc]
  | EAluw op a b iha ihb =>
      intro acc
      simp only [expr_vars]
      rw [iha (expr_vars b acc), ihb acc, iha (expr_vars b []), Bool.and_assoc]
  | EMd op a b iha ihb =>
      intro acc
      simp only [expr_vars]
      rw [iha (expr_vars b acc), ihb acc, iha (expr_vars b []), Bool.and_assoc]
  | EMdw op a b iha ihb =>
      intro acc
      simp only [expr_vars]
      rw [iha (expr_vars b acc), ihb acc, iha (expr_vars b []), Bool.and_assoc]
  | EExt sx lo n a iha => intro acc; simp only [expr_vars]; exact iha acc
  | EBlob sx k i n => intro acc; simp [expr_vars]

/-- The trie variant of `all_live` agrees with it. -/
theorem expr_all_live_t_eq (nx0 : Nat) (acc : List Nat) (t : ptree Unit) (e : expr)
    (H : live_agree acc t) : expr_all_live_t nx0 t e = all_live nx0 acc e := by
  induction e with
  | ELit z => rfl
  | EVar n =>
      have hH := H n
      by_cases h : n < nx0 <;> simp [expr_all_live_t, all_live, expr_vars, h, hH]
  | EAlu op a b iha ihb =>
      have hA := iha
      have hB := ihb
      simp only [expr_all_live_t, all_live, hA, hB, expr_vars]
      rw [forallb_expr_vars (fun v => decide (v < nx0) || acc.any (fun x => v == x)) a
            (expr_vars b [])]
      cases (expr_vars a []).all (fun v => decide (v < nx0) || acc.any (fun x => v == x)) <;> simp
  | EAluw op a b iha ihb =>
      have hA := iha
      have hB := ihb
      simp only [expr_all_live_t, all_live, hA, hB, expr_vars]
      rw [forallb_expr_vars (fun v => decide (v < nx0) || acc.any (fun x => v == x)) a
            (expr_vars b [])]
      cases (expr_vars a []).all (fun v => decide (v < nx0) || acc.any (fun x => v == x)) <;> simp
  | EMd op a b iha ihb =>
      have hA := iha
      have hB := ihb
      simp only [expr_all_live_t, all_live, hA, hB, expr_vars]
      rw [forallb_expr_vars (fun v => decide (v < nx0) || acc.any (fun x => v == x)) a
            (expr_vars b [])]
      cases (expr_vars a []).all (fun v => decide (v < nx0) || acc.any (fun x => v == x)) <;> simp
  | EMdw op a b iha ihb =>
      have hA := iha
      have hB := ihb
      simp only [expr_all_live_t, all_live, hA, hB, expr_vars]
      rw [forallb_expr_vars (fun v => decide (v < nx0) || acc.any (fun x => v == x)) a
            (expr_vars b [])]
      cases (expr_vars a []).all (fun v => decide (v < nx0) || acc.any (fun x => v == x)) <;> simp
  | EExt sx lo n a iha =>
      simp only [expr_all_live_t, all_live, expr_vars, iha]
  | EBlob sx k i n => rfl

/-- Filter with pointwise-equal predicates. -/
theorem filter_congr_b {α : Type} (l : List α) {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons a r ih =>
      have ha : p a = q a := h a (by simp)
      have hr : r.filter p = r.filter q :=
        ih (fun x hx => h x (by simp [hx]))
      simp only [List.filter_cons, ha, hr]

/-- The GC through the trie equals the reference GC. -/
theorem cs_gc_eq (nx0 : Nat) (cs : acs) : cs_gc nx0 cs = cs_gc_ref nx0 cs := by
  have H := live_vars_agree nx0 cs
  simp only [cs_gc, cs_gc_ref]
  congr 1
  apply filter_congr_b
  intro K _
  cases K <;>
    simp only [kn_gc_entry_t, kn_gc_entry, expr_all_live_t_eq nx0 _ _ _ H] <;>
    try (with_unfolding_all exact rfl)

/-! -/

/-- `page_up` rounds up to the next page. -/
theorem page_up_check : page_up 4097 = 8192 := by decide

/-- `page_up` is the identity on a page multiple. -/
theorem page_up_check0 : page_up 4096 = 4096 := by decide

/-- `vis_cost` charges the range, its shadow and the slack. -/
theorem vis_cost_check : vis_cost 4096 = 4096 + 512 + 16384 := by decide

/-- `salt2` drops a `SNil` operand. -/
theorem salt2_check : salt2 .SNil (.SExit 3) = .SExit 3 := by decide

/-- `salt2` keeps both operands otherwise. -/
theorem salt2_check2 : salt2 (.SExit 1) (.SExit 2) = .SAlt2 (.SExit 1) (.SExit 2) := by decide

/-- `shape_eqb` compares shapes. -/
theorem shape_eqb_check : shape_eqb (.SExit 3) (.SExit 3) = true := by decide

/-- `shape_eqb` distinguishes shapes. -/
theorem shape_eqb_check2 : shape_eqb (.SExit 3) (.SExit 4) = false := by decide

/-- `mkind_eqb` on holes. -/
theorem mkind_eqb_check : mkind_eqb .KHOLE .KHOLE = true := by decide

/-- `mkind_eqb` distinguishes kinds. -/
theorem mkind_eqb_check2 : mkind_eqb .KHOLE .KFOG = false := by decide

/-- a hole token is a token but not fog. -/
theorem is_hole_check : is_hole (AM (.ELit 0) (.ELit 4096) .KHOLE) = true := by decide

/-- a fog token is a token but not a hole. -/
theorem is_fog_check : is_fog (fog_token 4096) = true := by decide

/-- `kentry_eqb` on image entries. -/
theorem kentry_eqb_check : kentry_eqb (.KImg 1 2) (.KImg 1 2) = true := by decide

/-- `kentry_eqb` distinguishes image entries. -/
theorem kentry_eqb_check2 : kentry_eqb (.KImg 1 2) (.KImg 1 3) = false := by decide

/-- the AT_RANDOM entry is the blob `K_RND` of 16 bytes. -/
theorem atr_entry_check : atr_entry = .KBlob (SA e_atrb.1 e_atrb.2) (.ELit 16) K_RND := by decide

/-- `STOPS ASAN` lists the seven routine stops plus the five sealed self-loops. -/
theorem STOPS_check : (STOPS ASAN).length = 12 := by decide

/-- `ASAN`'s entry. -/
theorem ASAN_entry_check : ASAN.a_entry = 0x4ba64 := by decide

/-- `init_vis ASAN` starts with the image hull. -/
theorem init_vis_check : (init_vis ASAN).length = 2 := by decide

/-- the number of initial variables. -/
theorem NX0_check : NX0 = 9 := by decide

/-- `K_RND` is the auxv AT_RANDOM type mnemonic. -/
theorem K_RND_check : K_RND = 25 := by decide

/-- `cell eqb` on ledger kinds through `amap_eqb`. -/
theorem amap_eqb_check : amap_eqb (fog_token 8) (fog_token 8) = true := by decide

/-- `list_eqb` on literal lists. -/
theorem list_eqb_check : list_eqb (· == ·) [1, 2, 3] [1, 2, 3] = true := by decide

/-- `list_eqb` distinguishes different lengths. -/
theorem list_eqb_check2 : list_eqb (· == ·) [1, 2] [1, 2, 3] = false := by decide

/-- `nt_set`/`nt_get` round trip. -/
theorem nt_get_set_check : nt_get (nt_set [] 2 7) 2 = some 7 := by decide

/-- `nt_get` misses an untouched index. -/
theorem nt_get_set_check2 : nt_get (nt_set [] 2 7) 1 = none := by decide

/-- `mk_fwd` rejects a repeated source. -/
theorem mk_fwd_check : mk_fwd [(1, 2), (1, 3)] = none := by decide

/-- `mk_fwd` accepts distinct sources. -/
theorem mk_fwd_check2 : mk_fwd [(1, 2), (3, 4)] = some [none, some 2, none, some 4] := by decide

/-- `cover_x` on an empty knowledge covers nothing. -/
theorem cover_x_check : cover_x 2 [] (.ELit 0) 0 4 = false := by decide
