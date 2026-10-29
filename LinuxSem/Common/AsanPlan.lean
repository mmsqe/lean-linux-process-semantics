/-
 New node families: add the node function to a
    file imported here (it only needs AsanPlanCore), a constructor to
    [snode]/[xnode]/[plan], a dispatch line, and one Section hypothesis in
    AsanPlanSound.
  A plan is a deep-embedded itinerary; `check` walks it and returns the SHAPE
  (the trace-set skeleton, with named holes for the hand-offs to other
  certificates) or a diagnostic `(code, plan, state)`.  The soundness proof is
  in `AsanPlanSound` (not part of this file), with one Section hypothesis
  per extension node family.
 Nothing is deferred.   `lake env lean LinuxSem/Common/AsanPlan.lean` is silent.
  NOTES.
  - Lean HAS no section variables inserted at USE sites (only at declaration
    sites), so — as in `AsanPlanCore` / `AxSymExec3B` — the
    `Section WithSegs` context is threaded EXPLICITLY: every definition that
    needs part of `segs IT A nx0 LIMIT` takes it as leading explicit
    parameters in that fixed order.  A definition takes only the variables it
    actually uses, in the order the section discharged them, so the
    `AsanPlanSound` soundness theorems call them unchanged:
      * `node_sys A nx0 y cs`         (uses `A` and `nx0`),
      * `node_x segs A nx0 x args cs` (uses `segs`, `A` and `nx0`),
      * `check_all A chk k css`       (uses `A` only).
  - `Z` is `Int`, `nat` is `Nat`; `Z.leb`/`Z.ltb`/`Z.eqb` become `≤` / `<` /
    `==`; `Nat.leb`/`Nat.eqb` likewise; `negb` is `!`; `fold_left f l init`
    is `l.foldl f init`; `id` and `K` stay bound-variable names.
  - a `match ...  Reduction of a certificate's `check ... fuel ...` is therefore
    fuel-linear with the usual `brecOn` overhead; `cert_refl` evaluates it
    once (see `CertRefl`).
  - Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AsanPlanCore
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanPlan

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3B
open LinuxSem.Common.AsanPlanCore

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

section WithSegs

/-! ## 7. Plans -/

/-- one-child (deterministic) syscall nodes.
    mmap and mprotect are NOT deterministic (every arm may be refused) and
    have their own plan constructors `PMmap` / `PMmapIn` / `PMprotect`. -/
inductive snode : Type
  /-- munmap of a tracked entry -/
  | YMunmap
  /-- brk query (a0 = 0) or a PROVABLY BLOCKED grow -/
  | YBrk
  /-- set_tid_address -/
  | YSetTid
  deriving DecidableEq, Repr

/-- extension nodes (no syscall; model unchanged) -/
inductive xnode : Type
  /-- sanitizer internal_memset(s, c, n) -/
  | XIMemset
  /-- sanitizer internal_memcpy(d, s, n) -/
  | XIMemcpy
  /-- musl memset(s, c, n) -/
  | XMemset
  /-- musl memcpy(d, s, n) -/
  | XMemcpy
  /-- sanitizer mem_is_zero(beg, size), one-sided (all zero) -/
  | XMemIsZero
  /-- musl __init_libc: for (i=0; envp[i]; i++); -/
  | XEnvScan
  /-- musl __init_libc: program-name scan over argv[0] -/
  | XPnScan
  /-- facts about the initial stack image (argument block) -/
  | XLayout
  /-- sanitizer internal_strncpy(dst, "<sealed>", 4095) -/
  | XIStrncpy
  /-- allocator PopulateFreeArray fill loop; args = [ELit K]: describe the K top cells -/
  | XPopFree
  /-- the library call pni_sniff_header (a summary specific to one target binary) -/
  | XSniff
  deriving DecidableEq, Repr

/-- The plan syntax. -/
inductive plan : Type
  /-- run a block (to an ecall / stop pc / undecidable instruction), then k -/
  | PRun (stops : List Int) (k : plan)
  /-- value of e <= mid / > mid (e over initial variables) -/
  | PSplit (e : expr) (mid : Int) (k1 k2 : plan)
  /-- the same for ANY e: both children must yield the SAME shape -/
  | PCase2 (e : expr) (mid : Int) (k1 k2 : plan)
  /-- the two sides of a recorded KDisj between ranges based at b1 / b2; same shape -/
  | PCaseDisj (b1 b2 : expr) (k1 k2 : plan)
  /-- add: the shadows of the apart 8-aligned app ranges [b1,+n1) [b2,+n2) are apart -/
  | PShDisj (b1 n1 b2 n2 : expr) (k : plan)
  /-- the knowledge is contradictory (dead branch) -/
  | PContra
  /-- add a fact the checker verifies from the knowledge -/
  | PFact (K : kentry) (k : plan)
  /-- add KWord (b+off) n (literal) joined from n known literal bytes -/
  | PJoin (b : expr) (off : Int) (n : Nat) (k : plan)
  /-- drop the knowledge entries at these positions -/
  | PForget (ixs : List Nat) (k : plan)
  /-- drop every memory fact not provably apart from [b, b+n) -/
  | PDropRange (b : expr) (n : expr) (k : plan)
  /-- drop the content facts outside the keep windows of their base (`kn_keep`) -/
  | PGcKeep (ws : List (expr × expr)) (k : plan)
  /-- raise the next-variable counter to m (>= nxt) -/
  | PBump (m : Nat) (k : plan)
  /-- the listed registers := fresh variables -/
  | PHavoc (rs : List Nat) (k : plan)
  /-- every register / KWord value with more than K expression nodes := fresh variable -/
  | PHavocBig (K : Nat) (k : plan)
  /-- re-spell register r as base + 2^logc * (fresh variable) -/
  | PFresh (r : Nat) (logc : Int) (base : Option expr) (k : plan)
  /-- one-child syscall node at an ecall -/
  | PSys (y : snode) (k : plan)
  /-- mmap NULL-hint or FIXED over a free range: -ENOMEM child / grant child -/
  | PMmap (krefused kgranted : plan)
  /-- mmap FIXED inside one tracked entry: -ENOMEM (entry kept) / ok / -ENOMEM (range destroyed) -/
  | PMmapIn (kkept kok kdestroyed : plan)
  /-- mprotect rw of a PROT_NONE slice: -ENOMEM child / grant child -/
  | PMprotect (krefused kgranted : plan)
  /-- brk grow with both outcomes -/
  | PBrk2 (kblocked kgranted : plan)
  /-- extension node -/
  | PX (x : xnode) (args : List expr) (k : plan)
  /-- HOOKED extension node: `XN id args` (node functions supplied to `check`
      by other files: argument-string nodes, file IO ...) -/
  | PExt (id : Nat) (args : List expr) (k : plan)
  /-- HOOKED emitting node: `XE id args` = (fd, pieces, state); shape `SEmitP` -/
  | PEmit (id : Nat) (args : List expr) (k : plan)
  /-- HOOKED two-child node: `XB id args` = (state1, state2); shape `SAlt2` -/
  | PExt2 (id : Nat) (args : List expr) (k1 k2 : plan)
  /-- counted loop: iteration variable EVar J in [0,N),
      invariant template `inv` (havoc registers = EVar v, J < v < nxt inv),
      `body` from inv (+ 0 <= J < N) must reach `PNext` leaves entailing
      inv[J := J+1]; then `k` from inv[J := N] -/
  | PLoop (J : Nat) (N : expr) (inv : acs) (body k : plan)
  /-- leaf inside a loop body: back at the head, next iteration -/
  | PNext
  /-- hand-off leaf: the state entails the stored state `HS h` -/
  | PHandoff (h : Nat)
  /-- exit / exit_group leaf -/
  | PExit
  /-- leaf: the pc holds the sealed runtime's self-loop [jal x0,0] -/
  | PSpin
  /-- fog: tracked entry i becomes a "0 or 1 entry of size <= sz" token -/
  | PFog (i : Nat) (sz : Int) (k : plan)
  /-- fog: insert such a token (denoting no entry) at position i -/
  | PFogNew (i : Nat) (sz : Int) (k : plan)
  /-- add the app range [b, b+n) to the budgeted ghost set -/
  | PGhost (b n : expr) (k : plan)
  /-- the visible range (b, n) becomes a ghost range (shadow must read zero) -/
  | PUnvis (b n : expr) (k : plan)
  /-- forget the program break: a_brk := fresh variable in [lo, hi] -/
  | PHavocBrk (lo hi : Int) (k : plan)
  /-- introduce a fresh variable known to lie in [lo, hi] (meet-stable facts) -/
  | PIntro (lo hi : Int) (k : plan)
  /-- undecidable conditional branch at pc: run both arms to joinpc, re-join
      (differing registers and `rs` := fresh variables), continue with k -/
  | PDiamond (joinpc : Int) (rs : List Nat) (k : plan)
  /-- injective renaming of variables >= the GC bound (sources,targets) -/
  | PRename (m : List (Nat × Nat)) (k : plan)
  /-- the canonical dense renaming (first-occurrence order) -/
  | PCompact (k : plan)
  /-- INLINE JOIN: check `k` ONCE from the offline join state `js`;
      then `karms` from the current state, whose `PMerge j` leaves must entail `js`
      (`entails_h lo (nxt js)`: registers EVar v, lo <= v < nxt js, are havoc slots) -/
  | PVia (j : Nat) (js : acs) (lo : Nat) (karms k : plan)
  /-- leaf inside the arms of `PVia j`: re-join; yields the continuation's shape -/
  | PMerge (j : Nat)
  /-- the off-image range [b, b+n) covered by the knowledge becomes one KUnk entry -/
  | PAbstractCell (b : expr) (n : Int) (k : plan)
  /-- the value of the (first) KWord fact at each listed address := fresh variable -/
  | PHavocWords (bs : List expr) (k : plan)
  /-- register r := e when the knowledge proves reg r = e (`node_respell`) -/
  | PRespell (r : Nat) (e : expr) (k : plan)
  /-- `PMmapIn` whose refused-DESTROYED children remember the punched range as a
      FREE hole (KHOLE token), so that a later MAP_FIXED over exactly that range is a `PMmap` -/
  | PMmapInH (kkept kok kdestroyed : plan)
  deriving DecidableEq, Repr

/-! ## 8'. Node dispatch

     -/

/-- Dispatch of the one-child syscall nodes. -/
def node_sys (A : atable) (nx0 : Nat) (y : snode) (cs : acs) : Option acs :=
  match y with
  | .YMunmap => node_munmap A cs
  | .YBrk => node_brk1 A cs
  | .YSetTid => node_settid nx0 cs

/-- Dispatch of the extension nodes. -/
def node_x (segs : List Segment) (A : atable) (nx0 : Nat) (x : xnode)
    (args : List expr) (cs : acs) : Option acs :=
  match x with
  -- internal_memset replicates the raw a1: needs c < 256
  | .XIMemset => summary_fill A nx0 cs A.x_imemset 256
  | .XMemset => summary_fill A nx0 cs A.x_memset two64
  | .XIMemcpy => summary_copy A segs nx0 cs A.x_imemcpy
  | .XMemcpy => summary_copy A segs nx0 cs A.x_memcpy
  | .XMemIsZero => summary_miz A nx0 cs
  | .XEnvScan => node_envscan A cs
  | .XPnScan => node_pnscan A nx0 cs
  | .XLayout => node_layout cs args
  | .XIStrncpy => summary_istrncpy A nx0 cs
  | .XPopFree => summary_popfree A nx0 cs args
  | .XSniff => summary_sniff A segs nx0 cs

/-! ## 9. The checker -/

/-- Result of checking: the shape, or a diagnostic (code, remaining plan,
    state): 0 fuel, 1 block run failed (carry side conditions; state = START
    of the block), 2 not at an ecall, 3 node arguments rejected, 4 unknown hole. -/
inductive cres : Type
  | COk (s : shape)
  | CErr (code : Int) (where_ : plan) (cs : acs)
  deriving DecidableEq, Repr

section Check

/-- result codes: 0 fuel, 1 block run failed, 2 not at an ecall (PSpin: not at the self-loop), 3 node rejected,
    4 unknown hole, 6 PCase2/PCaseDisj children shapes differ, 7 loop body shape not SNext, 8 PNext outside a
    loop / PMerge outside its PVia, 9 variable counter below the loop's havoc range / the PVia's frozen bound.

    run the (same) child plan on every state of a non-empty list; all must
    succeed with syntactically equal shapes (used for the destroyed-case list
    of `PMmapIn`); code 6 = shapes differ, 3 = empty list. -/
def check_all (A : atable) (chk : acs → plan → cres) (k : plan) (css : List acs) : cres :=
  match css with
  | [] => .CErr 3 k (init_acs_of A)
  | cs0 :: rest =>
      match chk cs0 k with
      | .COk s0 =>
          rest.foldl
            (fun acc cs =>
              match acc with
              | .COk s =>
                  match chk cs k with
                  | .COk s' => if shape_eqb s s' then .COk s else .CErr 6 k cs
                  | err => err
              | err => err)
            (.COk s0)
      | err => err

/-- The checker.  `fuel` bounds the whole walk (`0` = out of fuel), `lc` is the
    loop / inline-join context, `cs` the current checker state, `p` the plan.

    Hooks: `XN` (extension nodes), `XE` (emitting nodes), `XB` (two-child
    nodes), `HS` (the stored hand-off states), `KC` (register cap for the
    extension-mode executor, 0 = off), `bfuel` (executor fuel per block). -/
def check_go (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel : Nat)
    (ck : Option loopctx → acs → plan → cres)
    (lc : Option loopctx) (cs : acs) (p : plan) : cres :=
    -- inside a loop body the variables below the havoc range must stay allocated
    -- (and are protected from GC)
    let gcb := match lc with | some c => lc_bnd c | none => nx0
    if !(match lc with | some c => lc_bnd c ≤ nxt cs | none => true) then .CErr 9 p cs
    else
    match p with
    | .PRun stops k =>
        match run_block_gc segs IT gcb KC bfuel (stops ++ STOPS A) cs with
        | some cs' => ck lc cs' k
        | none => .CErr 1 p cs
    | .PSplit e mid k1 k2 =>
        if expr_vars_lt nx0 e then
          match erange (kn cs) e with
          | some (lo, hi) =>
              if lo ≤ mid && mid < hi then
                match ck lc (set_kn cs (.KRange e lo mid :: kn cs)) k1 with
                | .COk s1 =>
                    match ck lc (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 with
                    | .COk s2 => .COk (.SCase e mid s1 s2)
                    | err => err
                | err => err
              -- decided by range: only the live child, its shape as is
              else if hi ≤ mid then ck lc cs k1 else ck lc cs k2
          | none => .CErr 3 p cs
        else .CErr 3 p cs
    | .PCase2 e mid k1 k2 =>
        match erange (kn cs) e with
        | some (lo, hi) =>
            if !(lo ≤ mid && mid < hi) then (if hi ≤ mid then ck lc cs k1 else ck lc cs k2)
            else
            if lo ≤ mid && mid < hi then
              let cs1 := set_kn cs (.KRange e lo mid :: kn cs)
              let cs2 := set_kn cs (.KRange e (mid + 1) hi :: kn cs)
              -- a child whose range fact is contradictory is unreachable: the other's shape
              if kn_contra (kn cs1) then ck lc cs2 k2
              else if kn_contra (kn cs2) then ck lc cs1 k1
              else
                match ck lc cs1 k1 with
                | .COk s1 =>
                    match ck lc cs2 k2 with
                    | .COk s2 => if shape_eqb s1 s2 then .COk s1 else .CErr 6 p cs
                    | err => err
                | err => err
            else .CErr 3 p cs
        | none => .CErr 3 p cs
    | .PCaseDisj b1 b2 k1 k2 =>
        match node_casedisj cs b1 b2 with
        | some (csa, csb) =>
            match ck lc csa k1 with
            | .COk s1 =>
                match ck lc csb k2 with
                | .COk s2 => if shape_eqb s1 s2 then .COk s1 else .CErr 6 p cs
                | err => err
            | err => err
        | none => .CErr 3 p cs
    | .PShDisj b1 n1 b2 n2 k =>
        match node_shdisj A cs b1 n1 b2 n2 with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PContra => if kn_contra (kn cs) then .COk .SNil else .CErr 3 p cs
    | .PFact K k => if fact_ok (kn cs) K then ck lc (add_kn cs [K]) k else .CErr 3 p cs
    | .PJoin b off n k =>
        match node_join segs cs b off n with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PForget ixs k => ck lc (set_kn cs (drop_ixs ixs 0 (kn cs))) k
    | .PDropRange b n k => ck lc (node_droprange cs b n) k
    | .PGcKeep ws k => ck lc (set_kn cs (kn_keep (kn cs) ws)) k
    | .PBump m k =>
        match node_bump cs m with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PHavoc rs k =>
        match node_havoc nx0 cs rs with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PHavocBig K k =>
        match node_havocbig nx0 cs K with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PFresh r logc base k =>
        match node_fresh nx0 cs r logc base with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PSys y k =>
        if is_ecall_at segs cs then
          match node_sys A nx0 y cs with
          | some cs' => ck lc cs' k
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    | .PBrk2 ka kb =>
        if is_ecall_at segs cs then
          match node_brk2 A LIMIT cs with
          | some (csa, csb) =>
              match ck lc csa ka with
              | .COk sa =>
                  match ck lc csb kb with
                  | .COk sb => .COk (salt2 sa sb)
                  | err => err
              | err => err
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    | .PMmap ka kb =>
        if is_ecall_at segs cs then
          match node_mmap2 A nx0 LIMIT cs with
          | some (csa, csb) =>
              match ck lc csa ka with
              | .COk sa =>
                  match ck lc csb kb with
                  | .COk sb => .COk (salt2 sa sb)
                  | err => err
              | err => err
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    | .PMmapIn ka kb kc =>
        if is_ecall_at segs cs then
          match node_mmapin A nx0 LIMIT false cs with
          | some (csa, csb, cscs) =>
              match ck lc csa ka with
              | .COk sa =>
                  match ck lc csb kb with
                  | .COk sb =>
                      match check_all A (ck lc) kc cscs with
                      | .COk sc => .COk (salt2 sa (salt2 sb sc))
                      | err => err
                  | err => err
              | err => err
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    -- as PMmapIn, destroyed children with the hole token
    | .PMmapInH ka kb kc =>
        if is_ecall_at segs cs then
          match node_mmapin A nx0 LIMIT true cs with
          | some (csa, csb, cscs) =>
              match ck lc csa ka with
              | .COk sa =>
                  match ck lc csb kb with
                  | .COk sb =>
                      match check_all A (ck lc) kc cscs with
                      | .COk sc => .COk (salt2 sa (salt2 sb sc))
                      | err => err
                  | err => err
              | err => err
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    | .PMprotect ka kb =>
        if is_ecall_at segs cs then
          match node_mprotect2 A LIMIT cs with
          | some (csa, csb) =>
              match ck lc csa ka with
              | .COk sa =>
                  match ck lc csb kb with
                  | .COk sb => .COk (salt2 sa sb)
                  | err => err
              | err => err
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    | .PX x args k =>
        match node_x segs A nx0 x args cs with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PExt id args k =>
        match XN id args cs with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PEmit id args k =>
        match XE id args cs with
        | some (fd, ps, cs') =>
            match ck lc cs' k with
            | .COk s => .COk (.SEmitP fd ps s)
            | err => err
        | none => .CErr 3 p cs
    | .PExt2 id args k1 k2 =>
        match XB id args cs with
        | some (csa, csb) =>
            match ck lc csa k1 with
            | .COk sa =>
                match ck lc csb k2 with
                | .COk sb => .COk (.SAlt2 sa sb)
                | err => err
            | err => err
        | none => .CErr 3 p cs
    | .PLoop J N inv body k =>
        match loop_ok nx0 cs J N inv with
        | some nhi =>
            let lo := J + 1
            let hi := nxt inv
            if pc inv == pc cs && entails_h A lo hi cs (inst inv J (.ELit 0)) then
              match ck (some (.LC (pc cs) (inst inv J (eaddz (.EVar J) 1)) lo hi))
                  (loop_body_state J N nhi inv) body with
              | .COk .SNext => ck lc (inst inv J N) k
              | .COk _ => .CErr 7 p cs
              | err => err
            else .CErr 3 p cs
        | none => .CErr 3 p cs
    | .PNext =>
        match lc with
        | some (.LC h nx lo hi) =>
            if pc cs == h && entails_h A lo hi cs nx then .COk .SNext else .CErr 3 p cs
        | _ => .CErr 8 p cs
    | .PHandoff h =>
        match HS h with
        | some ch => if entails cs ch then .COk (.SHole h) else .CErr 3 p cs
        | none => .CErr 4 p cs
    | .PExit =>
        if is_ecall_at segs cs then
          match node_exit cs with
          | some code => .COk (.SExit code)
          | none => .CErr 3 p cs
        else .CErr 2 p cs
    | .PSpin => if node_spin segs cs then .COk .SNil else .CErr 2 p cs
    | .PFog i sz k =>
        match node_fog cs i sz with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PFogNew i sz k =>
        match node_fognew cs i sz with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PGhost b n k =>
        match node_ghost LIMIT cs b n with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PUnvis b n k =>
        match node_unvis A cs b n with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PHavocBrk lo hi k =>
        match node_havocbrk nx0 cs lo hi with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PIntro lo hi k =>
        match node_intro nx0 cs lo hi with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PRename m k =>
        match node_rename gcb cs m with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PCompact k =>
        match node_compact gcb cs with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PVia j js lo karms k =>
        if via_ok nx0 cs js lo then
          match ck lc js k with
          | .COk sk => ck (some (.JC j js sk (nxt cs) lo)) cs karms
          | err => err
        else .CErr 3 p cs
    | .PMerge j =>
        match lc with
        | some (.JC j' js sk b lo) =>
            if j == j' && pc cs == pc js && shape_vars_lt nx0 sk
                && entails_h A lo (nxt js) cs js then .COk sk
            else .CErr 3 p cs
        | _ => .CErr 8 p cs
    | .PAbstractCell b n k =>
        match node_abstractcell A cs b n with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PHavocWords bs k =>
        match node_havocwords nx0 cs bs with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PRespell r e k =>
        match node_respell cs r e with
        | some cs' => ck lc cs' k
        | none => .CErr 3 p cs
    | .PDiamond joinpc rs k =>
        match branch_probe IT cs with
        | some e =>
            match erange (kn cs) e with
            | some (lo, hi) =>
                -- decided after all (by range): ONE arm = `PRun [joinpc] k`
                if hi < 1 || 0 < lo then
                  match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs with
                  | some cs' => if pc cs' == joinpc then ck lc cs' k else .CErr 3 p cs'
                  | none => .CErr 1 p cs
                else
                  let cs1 := set_kn cs (.KRange e lo 0 :: kn cs)
                  let cs2 := set_kn cs (.KRange e 1 hi :: kn cs)
                  match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs1 with
                  | some ca =>
                      match run_block_gc segs IT gcb KC bfuel (joinpc :: STOPS A) cs2 with
                      | some cb =>
                          match node_diamond_join A nx0 (nxt cs) joinpc rs ca cb with
                          | some csj => ck lc csj k
                          -- arms do not re-join: state = end of arm 1 (probe = 0)
                          | none => .CErr 3 p ca
                      | none => .CErr 1 p cs2
                  | none => .CErr 1 p cs1
            | none => .CErr 3 p cs
        | none => .CErr 2 p cs   -- not at a conditional branch

def check (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel : Nat) :
    Nat → Option loopctx → acs → plan → cres
  | 0, _, cs, p => .CErr 0 p cs
  | f + 1, lc, cs, p =>
    check_go segs IT A nx0 LIMIT XN XE XB HS KC bfuel
      (check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f) lc cs p

/-- **The successor equation, as a rewrite rule.**

    `check` is fuel-recursive, and `check_go` takes the recursive call as a
    parameter — so this equation is definitional (`rfl`) and gives every
    downstream proof a usable unfolding at `fuel = f + 1`.  (Before the
    refactor the recursive call sat inside a `let`, which made Lean compile
    `check` by course-of-values recursion and left no usable equation at all;
    see `AsanPlanSound`'s DEFERRED prose.) -/
theorem check_succ (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel f : Nat) (lc : Option loopctx) (cs : acs)
    (p : plan) :
    check segs IT A nx0 LIMIT XN XE XB HS KC bfuel (f + 1) lc cs p
      = check_go segs IT A nx0 LIMIT XN XE XB HS KC bfuel
          (check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f) lc cs p := rfl

end Check

end WithSegs

/-! ## Sanity checks

     `AsanPlan` states no lemma (its proofs live in `AsanPlanSound`),
    so these are this tree's own smoke tests: they pin the fuel case, both node
    dispatchers and the empty `check_all` case by definitional equality. -/

/-- fuel `0` fails with code 0 before looking at the state. -/
theorem check_zero (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel : Nat) (cs : acs) (p : plan) :
    check segs IT A nx0 LIMIT XN XE XB HS KC bfuel 0 none cs p = .CErr 0 p cs := rfl

/-- `check_all` on the empty state list is a code-3 diagnostic at the
    initial state of the image. -/
theorem check_all_nil (A : atable) (chk : acs → plan → cres) (k : plan) :
    check_all A chk k [] = .CErr 3 k (init_acs_of A) := rfl

/-- `PNext` outside a loop context is a code-8 diagnostic. -/
theorem check_pnext_no_loop (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel : Nat) (cs : acs) :
    check segs IT A nx0 LIMIT XN XE XB HS KC bfuel 1 none cs .PNext
      = .CErr 8 .PNext cs := rfl

/-- `PMerge` outside a `PVia` arm is a code-8 diagnostic. -/
theorem check_merge_no_via (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel j : Nat) (cs : acs) :
    check segs IT A nx0 LIMIT XN XE XB HS KC bfuel 1 none cs (.PMerge j)
      = .CErr 8 (.PMerge j) cs := rfl

/-- The fuel really recurses: a two-node plan walks through the first node
    (`PForget []`, which rewrites the knowledge into the same state) and stops
    at the second, on the state the first one produced.  (No segments, the
    empty instruction table and no limit are needed: neither node runs a
    block, and `PNext` is rejected before any syscall check.) -/
theorem check_two_nodes :
    check [] .PTLeaf ASAN NX0 0 (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ _ => none) (fun _ => none) 0 0 2 none (init_acs_of ASAN)
        (.PForget [] .PNext)
      = .CErr 8 .PNext (set_kn (init_acs_of ASAN) (kn (init_acs_of ASAN))) := rfl

/-- `node_sys` dispatches `YMunmap` to `node_munmap`. -/
theorem node_sys_munmap (A : atable) (nx0 : Nat) (cs : acs) :
    node_sys A nx0 .YMunmap cs = node_munmap A cs := rfl

/-- `node_sys` dispatches `YSetTid` to `node_settid`. -/
theorem node_sys_settid (A : atable) (nx0 : Nat) (cs : acs) :
    node_sys A nx0 .YSetTid cs = node_settid nx0 cs := rfl

/-- `node_x` dispatches `XLayout` to `node_layout`. -/
theorem node_x_layout (segs : List Segment) (A : atable) (nx0 : Nat)
    (args : List expr) (cs : acs) :
    node_x segs A nx0 .XLayout args cs = node_layout cs args := rfl

/-- `node_x` dispatches `XIMemset` to `summary_fill` at the image entry with
    the `c < 256` cap. -/
theorem node_x_imemset (segs : List Segment) (A : atable) (nx0 : Nat)
    (args : List expr) (cs : acs) :
    node_x segs A nx0 .XIMemset args cs = summary_fill A nx0 cs A.x_imemset 256 := rfl

/-- `node_x` dispatches `XSniff` to `summary_sniff`. -/
theorem node_x_sniff (segs : List Segment) (A : atable) (nx0 : Nat)
    (args : List expr) (cs : acs) :
    node_x segs A nx0 .XSniff args cs = summary_sniff A segs nx0 cs := rfl

/-- `cres`'s (Lean-only) Boolean equality accepts equal shapes. -/
theorem cres_eqb_check : ((.COk .SNext : cres) == .COk .SNext) = true := by decide

/-- ... and separates different ones. -/
theorem cres_eqb_check2 : ((.COk .SNext : cres) == .COk .SNil) = false := by decide

end LinuxSem.Common.AsanPlan
