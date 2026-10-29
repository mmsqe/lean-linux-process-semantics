/-
  * LinuxProcessSem.Checks.Sys.Fs.ReadWrite.Write — the `write` (64)
    checker's soundness and completeness

  The four `check_write_*` lemmas — `check_write_sound_ok`,
  `check_write_sound_unmodeled`, `check_write_complete_ok` and
  `check_write_complete_unmodeled` — split out of the parent module so
  that it stops growing as each quadruple lands (the rest live in
  `ReadWrite/Vec.lean` and `ReadWrite/Readv.lean`).

  The statements are the parent's `write_spec` / `check_write` verbatim;
  the helpers added here are marked in the sections below.

  WHAT `check_write` ADDS TO THE RECIPE.  The walk order is the parent
  header's item (10) — gate, then the `-EFAULT` `if`, then `place`, then
  `w_is0 count` — and three of the parent's footguns apply unchanged: the
  gate is split with `by_cases` and the gate-true side closed by
  `exact nomatch H` / `rfl`, the completeness leaves are INVERTED rather
  than `cases`d, and the `if` arms of the checker and the spec are split in
  the same `by_cases` so that `rw [ite_eq_left …] at H ⊢` rewrites both.

  THE CHANNEL ARM's delivered prefix.  `check_write` pins the return only
  through `ret.toNat`, while the spec's `choose` names a `ds` and returns
  `len_word ds`.  The Prelude already carries the round trip in the shape
  `pwrite64` needs it (`firstn_length_le_Z`, `len_word_firstn_ret`, over an
  `Int` index); the channel arm needs it at `ret.toNat ≤ bs.length` and on
  the prefix the checker actually names, so `length_take_of_le` /
  `len_word_take_eq` below restate it there.  The one ingredient `bitvec`
  does not give definitionally is `ofNat_toNat_eq`:
  `BitVec.ofNat 64 ret.toNat = ret` (the `% 2 ^ 64` is in the way).
-/
import LinuxSem.Checks.Sys.Fs.ReadWrite

namespace LinuxSem.Checks.Sys.Fs.ReadWrite

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Uaccess

/-! ### The delivered prefix of a channel write

  `check_write`'s channel arm accepts a claimed return `ret` whenever
  `1 ≤ ret.toNat ≤ bs.length` and the copy-in ledger is
  `[(buf, ret.toNat)]`; the spec asks for a `ds` with
  `ds = bs.take ds.length` and returns `len_word ds`.  So a proof of the
  sound direction has to move between `ret` and the prefix it names, and
  the lemmas below are the whole of that movement. -/

/-- `BitVec.ofNat 64` of a word's own `toNat` is the word.  `bitvec` does
    not give this definitionally: the `% 2 ^ 64` is in the way. -/
theorem ofNat_toNat_eq (w : word) : BitVec.ofNat 64 w.toNat = w := by
  refine BitVec.eq_of_toNat_eq ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

/-- The length of a prefix that stops inside the list is the
    index it stopped at. -/
theorem length_take_of_le {α : Type} (l : List α) (n : Nat) (h : n ≤ l.length) :
    (l.take n).length = n := by
  rw [List.length_take, Nat.min_eq_left h]

/-- An accepted channel write's ledger is a real prefix of the
    source, so the `choose` that the spec offers it can be satisfied at
    `ds := bs.take ret.toNat`. -/
theorem len_word_take_eq (bs : List byte) (ret : word)
    (h : ret.toNat ≤ bs.length) : len_word (bs.take ret.toNat) = ret := by
  unfold len_word
  rw [length_take_of_le bs ret.toNat h, ofNat_toNat_eq]

/-! ### The spec stages that cannot decline

  The completeness-unmodeled direction refutes every branch whose spec
  stage cannot produce `unmodeled`; these are the two the write arms
  reach that the parent file did not already have. -/

/-- `record_copyins reads (ret_only r)` never declines. -/
theorem record_copyins_ret_only_no_unmodeled (reads : List (word × Nat)) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ record_copyins reads
        (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r) i m .unmodeled := by
  unfold record_copyins LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
  refine bind_no_unmodeled _ _ i m (pure_no_unmodeled _ i m) ?_
  intro a m1 evs1 _
  exact pure_no_unmodeled _ i m1

/-- The pipe arm's whole leaf never declines. -/
theorem seqSpec_set_pipes_record_ret_only_no_unmodeled (ps : List (word × PipeBuf))
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model) :
    ¬ seqSpec (set_pipes ps) (record_copyins reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m .unmodeled :=
  modifySeq_no_unmodeled (with_pipes ps) _ i m
    (record_copyins_ret_only_no_unmodeled reads r i (with_pipes ps m))

/-- The channel arm's whole delivered-prefix leaf
    (`choose ;; emit ;; record_copyins ;; ret_only`) never declines. -/
theorem choose_deliver_no_unmodeled (P : List byte → Prop)
    (f : List byte → List event) (reads : List byte → List (word × Nat))
    (r : List byte → word) (i : SyscallInput) (m : Model) :
    ¬ bind (choose P)
        (fun ds => seqSpec (emit (f ds))
          (record_copyins (reads ds)
            (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only (r ds))))
        i m .unmodeled := by
  refine choose_bind_no_unmodeled P _ i m ?_
  intro ds
  exact emitSeq_no_unmodeled (f ds) _ i m
    (record_copyins_ret_only_no_unmodeled (reads ds) (r ds) i m)

/-- The two file arms' leaf — `set_fs` then `set_fds` round the
    ledger — never declines. -/
theorem seqSpec_set_fs_set_fds_no_unmodeled {A : Type} (fs' : Fs.Fs)
    (fds : List (word × FdEntry)) (k : SysSpec A) (i : SyscallInput) (m : Model)
    (hk : ¬ k i (with_fds fds (with_fs fs' m)) .unmodeled) :
    ¬ seqSpec (set_fs fs') (seqSpec (set_fds fds) k) i m .unmodeled := by
  refine modifySeq_no_unmodeled (with_fs fs') _ i m ?_
  exact modifySeq_no_unmodeled (with_fds fds) k i (with_fs fs' m) hk

/-! ### The leaves, built and inverted

  Each write arm ends in one of four shapes: a fixed return (`ret_only`),
  a recorded ledger (`record_copyins … (ret_only …)`), the same two
  rounded by `set_fs` / `set_fds` / `set_pipes`, or the channel's
  `choose`/`emit`.  The builders are what the sound directions need and
  the inversions what the completeness directions need, exactly as
  `seqSpec_set_fds_pure_ok` / `seqSpec_set_fds_pure_ok_inv` are for the
  read arms. -/

/-- The `FdFileW` / `FdFileRW` / `FdFileA` arms' zero-count
    leaf, at its own accepted outcome. -/
theorem seqSpec_set_fs_set_fds_ret_only_ok (fs' : Fs.Fs)
    (fds : List (word × FdEntry)) (r : word) (i : SyscallInput) (m : Model) :
    seqSpec (set_fs fs') (seqSpec (set_fds fds) (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m
      (.ok (mkEffect r [] []) (with_fds fds (with_fs fs' m)) []) := by
  refine ⟨(), with_fs fs' m, [], [], rfl, ?_, by simp⟩
  refine ⟨(), with_fds fds (with_fs fs' m), [], [], rfl, ?_, by simp⟩
  exact pure_ok _ i _

/-- The same two stages round a recorded ledger. -/
theorem seqSpec_set_fs_set_fds_record_ret_only_ok (fs' : Fs.Fs)
    (fds : List (word × FdEntry)) (reads : List (word × Nat)) (r : word)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_fs fs') (seqSpec (set_fds fds)
        (record_copyins reads (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r))) i m
      (.ok (with_copyins reads (mkEffect r [] []))
        (with_fds fds (with_fs fs' m)) []) := by
  refine ⟨(), with_fs fs' m, [], [], rfl, ?_, by simp⟩
  refine ⟨(), with_fds fds (with_fs fs' m), [], [], rfl, ?_, by simp⟩
  exact record_copyins_ok_empty rfl (pure_ok _ i _)

/-- Invert the zero-count leaf: the effect is the fixed return,
    the model is the two updates, and nothing was emitted. -/
theorem seqSpec_set_fs_set_fds_ret_only_ok_inv (fs' : Fs.Fs)
    (fds : List (word × FdEntry)) (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fs fs') (seqSpec (set_fds fds)
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m
      (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = with_fds fds (with_fs fs' m) ∧ evs = [] := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fs, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨u2, m2, ev3, ev4, h4, h5, h6⟩ := h2
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h4
  cases h4
  simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
    LinuxSem.LinuxProcessSem.pure] at h5
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/-- Invert the recorded-ledger leaf. -/
theorem seqSpec_set_fs_set_fds_record_ret_only_ok_inv (fs' : Fs.Fs)
    (fds : List (word × FdEntry)) (reads : List (word × Nat)) (r : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : seqSpec (set_fs fs') (seqSpec (set_fds fds)
      (record_copyins reads
        (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r))) i m
      (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] [])
      ∧ m' = with_fds fds (with_fs fs' m) ∧ evs = [] := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fs, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨u2, m2, ev3, ev4, h4, h5, h6⟩ := h2
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h4
  cases h4
  obtain ⟨core, hcore, heff⟩ :=
    record_copyins_ok_inv reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)
      i (with_fds fds (with_fs fs' m)) eff m' ev4 h5
  simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
    LinuxSem.LinuxProcessSem.pure] at hcore
  cases hcore
  simp only [mkEffect, List.append_nil] at heff
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases heff
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/-- The pipe arm's leaf, at its own accepted outcome. -/
theorem seqSpec_set_pipes_record_ret_only_ok (ps : List (word × PipeBuf))
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model) :
    seqSpec (set_pipes ps) (record_copyins reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m
      (.ok (with_copyins reads (mkEffect r [] [])) (with_pipes ps m) []) := by
  refine ⟨(), with_pipes ps m, [], [], rfl, ?_, by simp⟩
  exact record_copyins_ok_empty rfl (pure_ok _ i _)

/-- Invert the pipe arm's leaf. -/
theorem seqSpec_set_pipes_record_ret_only_ok_inv (ps : List (word × PipeBuf))
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_pipes ps) (record_copyins reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m
      (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] []) ∧ m' = with_pipes ps m ∧ evs = [] := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_pipes, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨core, hcore, heff⟩ :=
    record_copyins_ok_inv reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)
      i (with_pipes ps m) eff m' ev2 h2
  simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
    LinuxSem.LinuxProcessSem.pure] at hcore
  cases hcore
  simp only [mkEffect, List.append_nil] at heff
  simp only [List.append_nil] at h3
  cases heff
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/-- The channel arm's leaf, at its own accepted outcome. -/
theorem seqSpec_emit_record_ret_only_ok (evs0 : List event)
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model) :
    seqSpec (emit evs0) (record_copyins reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m
      (.ok (with_copyins reads (mkEffect r [] [])) m evs0) := by
  refine ⟨(), m, evs0, [], rfl, ?_, by simp⟩
  exact record_copyins_ok_empty rfl (pure_ok _ i _)

/-- Invert the channel arm's leaf: the emitted trace is the
    delivered bytes' events, the model is untouched, and the effect is the
    ledger round the delivered length. -/
theorem seqSpec_emit_record_ret_only_ok_inv (evs0 : List event)
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (emit evs0) (record_copyins reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)) i m
      (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] []) ∧ m' = m ∧ evs = evs0 := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  cases h1
  obtain ⟨core, hcore, heff⟩ :=
    record_copyins_ok_inv reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only r)
      i m eff m' ev2 h2
  simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
    LinuxSem.LinuxProcessSem.pure] at hcore
  cases hcore
  simp only [mkEffect, List.append_nil] at heff
  simp only [List.append_nil] at h3
  cases heff
  cases h3
  exact ⟨rfl, rfl, rfl⟩


/- =========================================================================
   write (64) — the sound directions
   ========================================================================= -/

/-- Soundness on accepted outcomes: whatever `check_write` accepts, the
    relational `write_spec` admits.  The walk is the parent header's item
    (9)(d): the count gate, then the `-EFAULT` `if`, then the arm's
    `place` (the file lookup and its gap guard), then `w_is0 count`, which
    picks `write_ledger`'s `ret_only` / `record_copyins` leaf and takes the
    `access_ok_zero` with it. -/
theorem check_write_sound_ok (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_write i fd buf count eff m = .CheckOk m' evs) :
    write_spec fd buf count i m (.ok eff m' evs) := by
  unfold write_spec write_range_gate write_file_tail write_ledger
  simp only [check_write] at H
  try dsimp only at H ⊢
  refine bind_ok0 (c := inputSpec) ?_ i m i m eff m' evs (input_ok i m) ?_
  try dsimp only
  refine bind_ok0 (c := getModelSpec) ?_ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
  cases q with
  | none =>
    try dsimp only at H ⊢
    exact ret_only_ok_spec H i
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at H ⊢
      by_cases hw : w_is0 ch = true
      · rw [ite_eq_left hw] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hw] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          exact nomatch H
        · rw [ite_eq_right hmr] at H ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
          · rw [ite_eq_right hc] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (bs.length == 0) = true
            · rw [ite_eq_left hz] at H ⊢
              exact ret_only_ok_spec H i
            · rw [ite_eq_right hz] at H ⊢
              try dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws <;> cases zs <;> cases us <;> cases cs
              · dsimp only at H
                by_cases hg : (decide (1 ≤ (ret.toNat : Int))
                    && decide ((ret.toNat : Int) ≤ (bs.length : Int))) = true
                · rw [ite_eq_left hg] at H
                  by_cases hr : access_ranges_eqb ks [(buf, ret.toNat)] = true
                  · rw [ite_eq_left hr] at H
                    cases H
                    have hgr : decide (1 ≤ (ret.toNat : Int)) = true
                        ∧ decide ((ret.toNat : Int) ≤ (bs.length : Int)) = true := by
                      simpa [Bool.and_eq_true] using hg
                    obtain ⟨h1d, h2d⟩ := hgr
                    have h1 : 1 ≤ (ret.toNat : Int) := of_decide_eq_true h1d
                    have h2 : (ret.toNat : Int) ≤ (bs.length : Int) := of_decide_eq_true h2d
                    have hkl : ks = [(buf, ret.toNat)] :=
                      (access_ranges_eqb_eq ks [(buf, ret.toNat)]).mp hr
                    rw [hkl]
                    have hbslen : ret.toNat ≤ bs.length := Int.ofNat_le.mp h2
                    have hlen : (bs.take ret.toNat).length = ret.toNat :=
                      length_take_of_le bs ret.toNat hbslen
                    have hcnt : (bs.length : Int) ≤ rw_count_clamp count := by
                      have hs := write_source_length_le i.in_mem buf count
                      rwa [hbs] at hs
                    have hlw : len_word (bs.take ret.toNat) = ret :=
                      len_word_take_eq bs ret hbslen
                    simp only [LinuxSem.LinuxProcessSem.bind]
                    refine ⟨bs.take ret.toNat, m, [],
                      List.map (event.WriteEv ch) (bs.take ret.toNat),
                      choose_ok (fun ds : List byte => 1 ≤ (ds.length : Int)
                          ∧ (ds.length : Int) ≤ rw_count_clamp count
                          ∧ ds = bs.take ds.length)
                        (bs.take ret.toNat) i m ⟨?_, ?_, ?_⟩, ?_, by simp⟩
                    · rw [hlen]; exact h1
                    · rw [hlen]; omega
                    · rw [hlen]
                    · rw [hlw, hlen]
                      exact seqSpec_emit_record_ret_only_ok _ _ _ i m
                  · rw [ite_eq_right hr] at H
                    exact nomatch H
                · rw [ite_eq_right hg] at H
                  exact nomatch H
              all_goals (try dsimp only at H)
              all_goals (try contradiction)
    | FdFile p off =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | FdFileW p off =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hmr] at H ⊢
        generalize hbs : write_source i.in_mem buf count = bs at H ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hz] at H ⊢
          try dsimp only at H ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at H ⊢
            ok_zsplit H buf count
            · cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  rw [ite_eq_left hw] at H ⊢
                  try dsimp only at H ⊢
                  obtain ⟨rfl, rfl, rfl⟩ :=
                    (check_ret_only_ok_iff eff (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFileW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs)) m)) [] m' evs).mp H
                  exact seqSpec_set_fs_set_fds_ret_only_ok _ _ _ i m
            · exact ret_only_ok_spec H i
          · rw [ite_eq_right hw] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at H
              exact nomatch H
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at H ⊢
                exact nomatch H
              · rw [ite_eq_right hmg] at H ⊢
                try dsimp only at H ⊢
                rw [ite_eq_right hw] at H ⊢
                try dsimp only at H ⊢
                obtain ⟨heff, hm', hevs⟩ :=
                  (check_ret_only_copyins_ok_iff [(buf, bs.length)] eff (len_word bs)
                    (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileW p (off + len_word bs)))
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs)) m)) [] m' evs).mp H
                subst heff
                subst hm'
                subst hevs
                exact seqSpec_set_fs_set_fds_record_ret_only_ok _ _ _ _ i m
    | FdFileA p off =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hmr] at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hak] at H ⊢
          by_cases hpos : rw_pos_einvalb off (count.toNat : Int) = true
          · rw [ite_eq_left hpos] at H ⊢
            exact ret_only_ok_spec H i
          · rw [ite_eq_right hpos] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at H ⊢
              exact ret_only_ok_spec H i
            · rw [ite_eq_right hz] at H ⊢
              try dsimp only at H ⊢
              by_cases hw : w_is0 count = true
              · rw [ite_eq_left hw] at H ⊢
                ok_zsplit H buf count
                · cases hfs : Fs.fs_lookup (m_fs m) p with
                  | none =>
                    simp only [hfs] at H
                    exact nomatch H
                  | some data =>
                    simp only [hfs] at H ⊢
                    try dsimp only at H ⊢
                    rw [ite_eq_left hw] at H ⊢
                    try dsimp only at H ⊢
                    obtain ⟨rfl, rfl, rfl⟩ :=
                      (check_ret_only_ok_iff eff (len_word bs)
                        (with_fds (fd_insert (m_fds m) fd
                            (FdEntry.FdFileA p (append_new_pos data bs off)))
                          (with_fs (Fs.fs_set (m_fs m) p
                            (Fs.file_write data (len_word data) bs)) m)) [] m' evs).mp H
                    exact seqSpec_set_fs_set_fds_ret_only_ok _ _ _ i m
                · exact ret_only_ok_spec H i
              · rw [ite_eq_right hw] at H ⊢
                cases hfs : Fs.fs_lookup (m_fs m) p with
                | none =>
                  simp only [hfs] at H
                  exact nomatch H
                | some data =>
                  simp only [hfs] at H ⊢
                  try dsimp only at H ⊢
                  rw [ite_eq_right hw] at H ⊢
                  try dsimp only at H ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    (check_ret_only_copyins_ok_iff [(buf, bs.length)] eff (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFileA p (append_new_pos data bs off)))
                        (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data (len_word data) bs)) m)) [] m' evs).mp H
                  subst heff
                  subst hm'
                  subst hevs
                  exact seqSpec_set_fs_set_fds_record_ret_only_ok _ _ _ _ i m
    | FdFileRW p off =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hmr] at H ⊢
        generalize hbs : write_source i.in_mem buf count = bs at H ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hz] at H ⊢
          try dsimp only at H ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at H ⊢
            ok_zsplit H buf count
            · cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  rw [ite_eq_left hw] at H ⊢
                  try dsimp only at H ⊢
                  obtain ⟨rfl, rfl, rfl⟩ :=
                    (check_ret_only_ok_iff eff (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFileRW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs)) m)) [] m' evs).mp H
                  exact seqSpec_set_fs_set_fds_ret_only_ok _ _ _ i m
            · exact ret_only_ok_spec H i
          · rw [ite_eq_right hw] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at H
              exact nomatch H
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at H ⊢
                exact nomatch H
              · rw [ite_eq_right hmg] at H ⊢
                try dsimp only at H ⊢
                rw [ite_eq_right hw] at H ⊢
                try dsimp only at H ⊢
                obtain ⟨heff, hm', hevs⟩ :=
                  (check_ret_only_copyins_ok_iff [(buf, bs.length)] eff (len_word bs)
                    (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileRW p (off + len_word bs)))
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs)) m)) [] m' evs).mp H
                subst heff
                subst hm'
                subst hevs
                exact seqSpec_set_fs_set_fds_record_ret_only_ok _ _ _ _ i m
    | FdDir =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | FdSocket sk =>
      try dsimp only at H ⊢
      exact nomatch H
    | FdPipe id w =>
      try dsimp only at H ⊢
      by_cases hwr : (!w) = true
      · rw [ite_eq_left hwr] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hwr] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          exact nomatch H
        · rw [ite_eq_right hmr] at H ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at H ⊢
            ok_zsplit H buf count
            · exact ret_only_ok_spec H i
            · exact ret_only_ok_spec H i
          · rw [ite_eq_right hc] at H ⊢
            by_cases hl : (!(pipe_end_live (m_fds m) id false)) = true
            · rw [ite_eq_left hl] at H ⊢
              exact nomatch H
            · rw [ite_eq_right hl] at H ⊢
              generalize hp : pipe_lookup (m_pipes m) id = p at H ⊢
              cases p with
              | none =>
                try dsimp only at H ⊢
                exact nomatch H
              | some st =>
                try dsimp only at H ⊢
                by_cases hroom : (!(pipe_write_room st (count.toNat : Int))) = true
                · rw [ite_eq_left hroom] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hroom] at H ⊢
                  generalize hbs : write_source i.in_mem buf count = bs at H ⊢
                  by_cases hfull : (!(bs.length == word_to_nat count)) = true
                  · rw [ite_eq_left hfull] at H ⊢
                    exact nomatch H
                  · rw [ite_eq_right hfull] at H ⊢
                    try dsimp only at H ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      (check_ret_only_copyins_ok_iff [(buf, bs.length)] eff count
                        (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m)
                        [] m' evs).mp H
                    subst heff
                    subst hm'
                    subst hevs
                    exact seqSpec_set_pipes_record_ret_only_ok _ _ _ i m
    | FdDevNull rd wr =>
      try dsimp only at H ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hwr] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          exact nomatch H
        · rw [ite_eq_right hmr] at H ⊢
          ok_zsplit H buf count
          · exact ret_only_ok_spec H i
          · exact ret_only_ok_spec H i
    | FdUrandom =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i


/- =========================================================================
   write (64) — the decline directions
   ========================================================================= -/

/-- Soundness on declines: wherever `check_write` fails closed, so does
    `write_spec`.  Every arm's decline is one of the gate, the missing
    path, the unrepresentable hole, the pipe's four, or the socket's
    permanent one; the leaf at the end of each is refuted from the
    checker's side with the parent's no-decline toolkit. -/
theorem check_write_sound_unmodeled (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_write i fd buf count eff m = .CheckUnmodeled) :
    write_spec fd buf count i m .unmodeled := by
  unfold write_spec write_range_gate write_file_tail write_ledger
  simp only [check_write] at H
  try dsimp only at H ⊢
  refine bind_unmodeled2 (c := inputSpec) ?_ i m i m [] (input_ok i m) ?_
  try dsimp only
  refine bind_unmodeled2 (c := getModelSpec) ?_ i m m m [] rfl ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
  cases q with
  | none =>
    try dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at H ⊢
      by_cases hw : w_is0 ch = true
      · rw [ite_eq_left hw] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hw] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          exact unmodeled_intro i m
        · rw [ite_eq_right hmr] at H ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at H ⊢
            simp only [check_access_ok_zero] at H
            by_cases hok : access_okb buf (count.toNat : Int) = true
            · rw [ite_eq_left hok] at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
            · rw [ite_eq_right hok] at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hc] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (bs.length == 0) = true
            · rw [ite_eq_left hz] at H ⊢
              exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hz] at H ⊢
              try dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws <;> cases zs <;> cases us <;> cases cs
              · dsimp only at H
                by_cases hg : (decide (1 ≤ (ret.toNat : Int))
                    && decide ((ret.toNat : Int) ≤ (bs.length : Int))) = true
                · rw [ite_eq_left hg] at H
                  by_cases hr : access_ranges_eqb ks [(buf, ret.toNat)] = true
                  · rw [ite_eq_left hr] at H
                    exact nomatch H
                  · rw [ite_eq_right hr] at H
                    exact nomatch H
                · rw [ite_eq_right hg] at H
                  exact nomatch H
              all_goals (try dsimp only at H)
              all_goals (try contradiction)
    | FdFile p off =>
      try dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | FdFileW p off =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hmr] at H ⊢
        generalize hbs : write_source i.in_mem buf count = bs at H ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at H ⊢
          exact absurd H
            (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hz] at H ⊢
          try dsimp only at H ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at H ⊢
            simp only [check_access_ok_zero] at H
            simp only [access_ok_zero]
            by_cases hok : access_okb buf (count.toNat : Int) = true
            · rw [ite_eq_left hok] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                try dsimp only at H ⊢
                exact unmodeled_intro i m
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact unmodeled_intro i m
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  rw [ite_eq_left hw] at H ⊢
                  try dsimp only at H ⊢
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (len_word bs) _ [])
            · rw [ite_eq_right hok] at H ⊢
              exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hw] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              try dsimp only at H ⊢
              exact unmodeled_intro i m
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at H ⊢
                exact unmodeled_intro i m
              · rw [ite_eq_right hmg] at H ⊢
                try dsimp only at H ⊢
                rw [ite_eq_right hw] at H ⊢
                try dsimp only at H ⊢
                exact absurd H
                  (check_ret_only_copyins_no_unmodeled [(buf, bs.length)]
                    eff (len_word bs) _ [])
    | FdFileA p off =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hmr] at H ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at H ⊢
          exact absurd H
            (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hak] at H ⊢
          by_cases hpos : rw_pos_einvalb off (count.toNat : Int) = true
          · rw [ite_eq_left hpos] at H ⊢
            exact absurd H
              (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hpos] at H ⊢
            generalize hbs : write_source i.in_mem buf count = bs at H ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at H ⊢
              exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hz] at H ⊢
              try dsimp only at H ⊢
              by_cases hw : w_is0 count = true
              · rw [ite_eq_left hw] at H ⊢
                simp only [check_access_ok_zero] at H
                simp only [access_ok_zero]
                by_cases hok : access_okb buf (count.toNat : Int) = true
                · rw [ite_eq_left hok] at H ⊢
                  cases hfs : Fs.fs_lookup (m_fs m) p with
                  | none =>
                    try dsimp only at H ⊢
                    exact unmodeled_intro i m
                  | some data =>
                    simp only [hfs] at H ⊢
                    try dsimp only at H ⊢
                    rw [ite_eq_left hw] at H ⊢
                    try dsimp only at H ⊢
                    exact absurd H
                      (check_ret_only_no_unmodeled eff (len_word bs) _ [])
                · rw [ite_eq_right hok] at H ⊢
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
              · rw [ite_eq_right hw] at H ⊢
                cases hfs : Fs.fs_lookup (m_fs m) p with
                | none =>
                  try dsimp only at H ⊢
                  exact unmodeled_intro i m
                | some data =>
                  simp only [hfs] at H ⊢
                  try dsimp only at H ⊢
                  rw [ite_eq_right hw] at H ⊢
                  try dsimp only at H ⊢
                  exact absurd H
                    (check_ret_only_copyins_no_unmodeled [(buf, bs.length)]
                      eff (len_word bs) _ [])
    | FdFileRW p off =>
      try dsimp only at H ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hmr] at H ⊢
        generalize hbs : write_source i.in_mem buf count = bs at H ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at H ⊢
          exact absurd H
            (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · rw [ite_eq_right hz] at H ⊢
          try dsimp only at H ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at H ⊢
            simp only [check_access_ok_zero] at H
            simp only [access_ok_zero]
            by_cases hok : access_okb buf (count.toNat : Int) = true
            · rw [ite_eq_left hok] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                try dsimp only at H ⊢
                exact unmodeled_intro i m
              | some data =>
                simp only [hfs] at H ⊢
                try dsimp only at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact unmodeled_intro i m
                · rw [ite_eq_right hmg] at H ⊢
                  try dsimp only at H ⊢
                  rw [ite_eq_left hw] at H ⊢
                  try dsimp only at H ⊢
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (len_word bs) _ [])
            · rw [ite_eq_right hok] at H ⊢
              exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hw] at H ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              try dsimp only at H ⊢
              exact unmodeled_intro i m
            | some data =>
              simp only [hfs] at H ⊢
              try dsimp only at H ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at H ⊢
                exact unmodeled_intro i m
              · rw [ite_eq_right hmg] at H ⊢
                try dsimp only at H ⊢
                rw [ite_eq_right hw] at H ⊢
                try dsimp only at H ⊢
                exact absurd H
                  (check_ret_only_copyins_no_unmodeled [(buf, bs.length)]
                    eff (len_word bs) _ [])
    | FdDir =>
      try dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | FdSocket sk =>
      try dsimp only at H ⊢
      exact unmodeled_intro i m
    | FdPipe id w =>
      try dsimp only at H ⊢
      by_cases hwr : (!w) = true
      · rw [ite_eq_left hwr] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hwr] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          exact unmodeled_intro i m
        · rw [ite_eq_right hmr] at H ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at H ⊢
            simp only [check_access_ok_zero] at H
            by_cases hok : access_okb buf (count.toNat : Int) = true
            · rw [ite_eq_left hok] at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
            · rw [ite_eq_right hok] at H
              exact absurd H
                (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · rw [ite_eq_right hc] at H ⊢
            by_cases hl : (!(pipe_end_live (m_fds m) id false)) = true
            · rw [ite_eq_left hl] at H ⊢
              exact unmodeled_intro i m
            · rw [ite_eq_right hl] at H ⊢
              generalize hp : pipe_lookup (m_pipes m) id = p at H ⊢
              cases p with
              | none =>
                try dsimp only at H ⊢
                exact unmodeled_intro i m
              | some st =>
                try dsimp only at H ⊢
                by_cases hroom : (!(pipe_write_room st (count.toNat : Int))) = true
                · rw [ite_eq_left hroom] at H ⊢
                  exact unmodeled_intro i m
                · rw [ite_eq_right hroom] at H ⊢
                  generalize hbs : write_source i.in_mem buf count = bs at H ⊢
                  by_cases hfull : (!(bs.length == word_to_nat count)) = true
                  · rw [ite_eq_left hfull] at H ⊢
                    exact unmodeled_intro i m
                  · rw [ite_eq_right hfull] at H ⊢
                    try dsimp only at H ⊢
                    exact absurd H
                      (check_ret_only_copyins_no_unmodeled [(buf, bs.length)]
                        eff count _ [])
    | FdDevNull rd wr =>
      try dsimp only at H ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hwr] at H ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at H ⊢
          exact unmodeled_intro i m
        · rw [ite_eq_right hmr] at H ⊢
          simp only [check_access_ok_zero] at H
          by_cases hok : access_okb buf (count.toNat : Int) = true
          · rw [ite_eq_left hok] at H
            exact absurd H
              (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 (rw_count_clamp count)) m [])
          · rw [ite_eq_right hok] at H
            exact absurd H
              (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    | FdUrandom =>
      try dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])


/- =========================================================================
   write (64) — the completeness directions

   These invert the spec's outcome instead of building it: the
   prologue is peeled with [bind_input_spec] / [bind_getModel], the
   checker is the GOAL, and every leaf is inverted with the
   `…_ok_inv` lemmas above (the parent's item (9)(a): `cases Hs` is only
   enough where the leaf is a `pure`).  The channel arm's delivered prefix
   is the spec's own `choose` witness, replayed through the checker's
   two-sided guard with [len_word_unsigned] and `ds = bs.take ds.length`.
   ========================================================================= -/

theorem check_write_complete_ok (i : SyscallInput) (fd buf count : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hs : write_spec fd buf count i m (.ok eff m' evs)) :
    check_write i fd buf count eff m = .CheckOk m' evs := by
  unfold write_spec write_range_gate write_file_tail write_ledger at Hs
  simp only [check_write]
  try dsimp only at Hs ⊢
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    cases Hs
    try simp [check_ret_only, bv_eqb_refl]
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at Hs ⊢
      by_cases hw : w_is0 ch = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hw] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hmr] at Hs ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hc] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (bs.length == 0) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hz] at Hs ⊢
              try dsimp only at Hs ⊢
              obtain ⟨ds, hP, Hk⟩ := choose_bind_ok_inv _ _ i m eff m' evs Hs
              obtain ⟨hd1, hd2, htake⟩ := hP
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_emit_record_ret_only_ok_inv _ _ _ i m eff m' evs Hk
              subst heff
              subst hm'
              subst hevs
              simp only [with_copyins]
              have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
              have hlt : (ds.length : Int) < two_pow_64 := by
                have h := (rw_count_clamp_range count).2
                have hc' : rw_count_clamp count ≤ (0x7ffff000 : Int) := by
                  simpa [MAX_RW_COUNT] using h
                rw [h2p]; omega
              have hlen : (len_word ds).toNat = ds.length := by
                have h := len_word_unsigned ds hlt
                omega
              have hlen_nat : ds.length ≤ bs.length := by
                have h2 : ds.length = (bs.take ds.length).length :=
                  congrArg List.length htake
                rw [h2, List.length_take]
                exact Nat.min_le_right _ _
              have hdle : (ds.length : Int) ≤ (bs.length : Int) := by omega
              have hcond : (decide (1 ≤ ((len_word ds).toNat : Int))
                  && decide (((len_word ds).toNat : Int) ≤ (bs.length : Int))) = true := by
                rw [hlen, decide_eq_true hd1, decide_eq_true hdle]
                rfl
              have hranges : access_ranges_eqb [(buf, ds.length)]
                  [(buf, (len_word ds).toNat)] = true := by
                rw [hlen]
                exact access_ranges_eqb_refl [(buf, ds.length)]
              rw [ite_eq_left hcond, ite_eq_left hranges, hlen, ← htake]
    | FdFile p off =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | FdFileW p off =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hmr] at Hs ⊢
        generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hz] at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                try dsimp only at Hs ⊢
                cases Hs
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  cases Hs
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  rw [ite_eq_left hw] at Hs ⊢
                  try dsimp only at Hs ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_set_fs_set_fds_ret_only_ok_inv _ _ _ i m eff m' evs Hs
                  subst heff
                  subst hm'
                  subst hevs
                  try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hw] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs
              try dsimp only at Hs ⊢
              cases Hs
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at Hs ⊢
                cases Hs
              · rw [ite_eq_right hmg] at Hs ⊢
                try dsimp only at Hs ⊢
                rw [ite_eq_right hw] at Hs ⊢
                try dsimp only at Hs ⊢
                obtain ⟨heff, hm', hevs⟩ :=
                  seqSpec_set_fs_set_fds_record_ret_only_ok_inv _ _ _ _ i m eff m' evs Hs
                subst heff
                subst hm'
                subst hevs
                exact check_ret_only_copyins_refl [(buf, bs.length)] (len_word bs) _ []
    | FdFileA p off =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hmr] at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (count.toNat : Int) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hpos] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hz] at Hs ⊢
              try dsimp only at Hs ⊢
              by_cases hw : w_is0 count = true
              · rw [ite_eq_left hw] at Hs ⊢
                ok_zsplit_c Hs buf count
                · cases hfs : Fs.fs_lookup (m_fs m) p with
                  | none =>
                    simp only [hfs] at Hs
                    try dsimp only at Hs ⊢
                    cases Hs
                  | some data =>
                    simp only [hfs] at Hs ⊢
                    try dsimp only at Hs ⊢
                    rw [ite_eq_left hw] at Hs ⊢
                    try dsimp only at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      seqSpec_set_fs_set_fds_ret_only_ok_inv _ _ _ i m eff m' evs Hs
                    subst heff
                    subst hm'
                    subst hevs
                    try simp [check_ret_only, bv_eqb_refl]
                · cases Hs
                  try simp [check_ret_only, bv_eqb_refl]
              · rw [ite_eq_right hw] at Hs ⊢
                cases hfs : Fs.fs_lookup (m_fs m) p with
                | none =>
                  simp only [hfs] at Hs
                  try dsimp only at Hs ⊢
                  cases Hs
                | some data =>
                  simp only [hfs] at Hs ⊢
                  try dsimp only at Hs ⊢
                  rw [ite_eq_right hw] at Hs ⊢
                  try dsimp only at Hs ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_set_fs_set_fds_record_ret_only_ok_inv _ _ _ _ i m eff m' evs Hs
                  subst heff
                  subst hm'
                  subst hevs
                  exact check_ret_only_copyins_refl [(buf, bs.length)] (len_word bs) _ []
    | FdFileRW p off =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hmr] at Hs ⊢
        generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at Hs ⊢
          cases Hs
          try simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hz] at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                try dsimp only at Hs ⊢
                cases Hs
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  cases Hs
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  rw [ite_eq_left hw] at Hs ⊢
                  try dsimp only at Hs ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_set_fs_set_fds_ret_only_ok_inv _ _ _ i m eff m' evs Hs
                  subst heff
                  subst hm'
                  subst hevs
                  try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hw] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs
              try dsimp only at Hs ⊢
              cases Hs
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at Hs ⊢
                cases Hs
              · rw [ite_eq_right hmg] at Hs ⊢
                try dsimp only at Hs ⊢
                rw [ite_eq_right hw] at Hs ⊢
                try dsimp only at Hs ⊢
                obtain ⟨heff, hm', hevs⟩ :=
                  seqSpec_set_fs_set_fds_record_ret_only_ok_inv _ _ _ _ i m eff m' evs Hs
                subst heff
                subst hm'
                subst hevs
                exact check_ret_only_copyins_refl [(buf, bs.length)] (len_word bs) _ []
    | FdDir =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | FdSocket sk =>
      try dsimp only at Hs ⊢
      cases Hs
    | FdPipe id w =>
      try dsimp only at Hs ⊢
      by_cases hwr : (!w) = true
      · rw [ite_eq_left hwr] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hwr] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hmr] at Hs ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
            · cases Hs
              try simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hc] at Hs ⊢
            by_cases hl : (!(pipe_end_live (m_fds m) id false)) = true
            · rw [ite_eq_left hl] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hl] at Hs ⊢
              generalize hp : pipe_lookup (m_pipes m) id = p at Hs ⊢
              cases p with
              | none =>
                try dsimp only at Hs ⊢
                cases Hs
              | some st =>
                try dsimp only at Hs ⊢
                by_cases hroom : (!(pipe_write_room st (count.toNat : Int))) = true
                · rw [ite_eq_left hroom] at Hs ⊢
                  cases Hs
                · rw [ite_eq_right hroom] at Hs ⊢
                  generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
                  by_cases hfull : (!(bs.length == word_to_nat count)) = true
                  · rw [ite_eq_left hfull] at Hs ⊢
                    cases Hs
                  · rw [ite_eq_right hfull] at Hs ⊢
                    try dsimp only at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      seqSpec_set_pipes_record_ret_only_ok_inv _ _ _ i m eff m' evs Hs
                    subst heff
                    subst hm'
                    subst hevs
                    exact check_ret_only_copyins_refl [(buf, bs.length)] count _ []
    | FdDevNull rd wr =>
      try dsimp only at Hs ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hwr] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hmr] at Hs ⊢
          ok_zsplit_c Hs buf count
          · cases Hs
            try simp [check_ret_only, bv_eqb_refl]
          · cases Hs
            try simp [check_ret_only, bv_eqb_refl]
    | FdUrandom =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]


/-- Completeness on declines: wherever `write_spec` fails closed,
    `check_write` does too.  Every branch whose spec stage CANNOT decline
    is knocked out with the parent's no-decline toolkit — the effect
    cascade is the SOUND direction's problem, not this one (parent header,
    item (9)(c)) — and the branches that carry a real decline close by
    `rfl` once the checker's own `if` is rewritten. -/
theorem check_write_complete_unmodeled (i : SyscallInput) (fd buf count : word)
    (m : Model) (eff : SyscallEffect)
    (Hs : write_spec fd buf count i m .unmodeled) :
    check_write i fd buf count eff m = .CheckUnmodeled := by
  unfold write_spec write_range_gate write_file_tail write_ledger at Hs
  simp only [check_write]
  try dsimp only at Hs ⊢
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    cases Hs
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at Hs ⊢
      by_cases hw : w_is0 ch = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hw] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          try rfl
        · rw [ite_eq_right hmr] at Hs ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at Hs ⊢
            ok_zsplit_c Hs buf count
            · exact absurd Hs (pure_no_unmodeled _ i m)
            · cases Hs
          · rw [ite_eq_right hc] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (bs.length == 0) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hz] at Hs ⊢
              try dsimp only at Hs ⊢
              exact absurd Hs (choose_deliver_no_unmodeled _ _ _ _ i m)
    | FdFile p off =>
      try dsimp only at Hs ⊢
      cases Hs
    | FdFileW p off =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        try rfl
      · rw [ite_eq_right hmr] at Hs ⊢
        generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hz] at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                try dsimp only at Hs ⊢
                try rfl
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  try rfl
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  rw [ite_eq_left hw] at Hs ⊢
                  try dsimp only at Hs ⊢
                  exact absurd Hs (seqSpec_set_fs_set_fds_no_unmodeled _ _ _ i m
                    (pure_no_unmodeled _ i _))
            · cases Hs
          · rw [ite_eq_right hw] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs
              try dsimp only at Hs ⊢
              try rfl
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at Hs ⊢
                try rfl
              · rw [ite_eq_right hmg] at Hs ⊢
                try dsimp only at Hs ⊢
                rw [ite_eq_right hw] at Hs ⊢
                try dsimp only at Hs ⊢
                exact absurd Hs (seqSpec_set_fs_set_fds_no_unmodeled _ _ _ i m
                  (record_copyins_ret_only_no_unmodeled _ _ i _))
    | FdFileA p off =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        try rfl
      · rw [ite_eq_right hmr] at Hs ⊢
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left hak] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hak] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (count.toNat : Int) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            cases Hs
          · rw [ite_eq_right hpos] at Hs ⊢
            generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left hz] at Hs ⊢
              cases Hs
            · rw [ite_eq_right hz] at Hs ⊢
              try dsimp only at Hs ⊢
              by_cases hw : w_is0 count = true
              · rw [ite_eq_left hw] at Hs ⊢
                ok_zsplit_c Hs buf count
                · cases hfs : Fs.fs_lookup (m_fs m) p with
                  | none =>
                    simp only [hfs] at Hs
                    try dsimp only at Hs ⊢
                    try rfl
                  | some data =>
                    simp only [hfs] at Hs ⊢
                    try dsimp only at Hs ⊢
                    rw [ite_eq_left hw] at Hs ⊢
                    try dsimp only at Hs ⊢
                    exact absurd Hs (seqSpec_set_fs_set_fds_no_unmodeled _ _ _ i m
                      (pure_no_unmodeled _ i _))
                · cases Hs
              · rw [ite_eq_right hw] at Hs ⊢
                cases hfs : Fs.fs_lookup (m_fs m) p with
                | none =>
                  simp only [hfs] at Hs
                  try dsimp only at Hs ⊢
                  try rfl
                | some data =>
                  simp only [hfs] at Hs ⊢
                  try dsimp only at Hs ⊢
                  rw [ite_eq_right hw] at Hs ⊢
                  try dsimp only at Hs ⊢
                  exact absurd Hs (seqSpec_set_fs_set_fds_no_unmodeled _ _ _ i m
                    (record_copyins_ret_only_no_unmodeled _ _ i _))
    | FdFileRW p off =>
      try dsimp only at Hs ⊢
      by_cases hmr : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left hmr] at Hs ⊢
        try rfl
      · rw [ite_eq_right hmr] at Hs ⊢
        generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left hz] at Hs ⊢
          cases Hs
        · rw [ite_eq_right hz] at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases hw : w_is0 count = true
          · rw [ite_eq_left hw] at Hs ⊢
            ok_zsplit_c Hs buf count
            · cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                try dsimp only at Hs ⊢
                try rfl
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  try rfl
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  rw [ite_eq_left hw] at Hs ⊢
                  try dsimp only at Hs ⊢
                  exact absurd Hs (seqSpec_set_fs_set_fds_no_unmodeled _ _ _ i m
                    (pure_no_unmodeled _ i _))
            · cases Hs
          · rw [ite_eq_right hw] at Hs ⊢
            cases hfs : Fs.fs_lookup (m_fs m) p with
            | none =>
              simp only [hfs] at Hs
              try dsimp only at Hs ⊢
              try rfl
            | some data =>
              simp only [hfs] at Hs ⊢
              try dsimp only at Hs ⊢
              by_cases hmg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hmg] at Hs ⊢
                try rfl
              · rw [ite_eq_right hmg] at Hs ⊢
                try dsimp only at Hs ⊢
                rw [ite_eq_right hw] at Hs ⊢
                try dsimp only at Hs ⊢
                exact absurd Hs (seqSpec_set_fs_set_fds_no_unmodeled _ _ _ i m
                  (record_copyins_ret_only_no_unmodeled _ _ i _))
    | FdDir =>
      try dsimp only at Hs ⊢
      cases Hs
    | FdSocket sk =>
      try dsimp only at Hs ⊢
      try rfl
    | FdPipe id w =>
      try dsimp only at Hs ⊢
      by_cases hwr : (!w) = true
      · rw [ite_eq_left hwr] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hwr] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          try rfl
        · rw [ite_eq_right hmr] at Hs ⊢
          by_cases hc : w_is0 count = true
          · rw [ite_eq_left hc] at Hs ⊢
            ok_zsplit_c Hs buf count
            · exact absurd Hs (pure_no_unmodeled _ i m)
            · cases Hs
          · rw [ite_eq_right hc] at Hs ⊢
            by_cases hl : (!(pipe_end_live (m_fds m) id false)) = true
            · rw [ite_eq_left hl] at Hs ⊢
              try rfl
            · rw [ite_eq_right hl] at Hs ⊢
              generalize hp : pipe_lookup (m_pipes m) id = p at Hs ⊢
              cases p with
              | none =>
                try dsimp only at Hs ⊢
                try rfl
              | some st =>
                try dsimp only at Hs ⊢
                by_cases hroom : (!(pipe_write_room st (count.toNat : Int))) = true
                · rw [ite_eq_left hroom] at Hs ⊢
                  try rfl
                · rw [ite_eq_right hroom] at Hs ⊢
                  generalize hbs : write_source i.in_mem buf count = bs at Hs ⊢
                  by_cases hfull : (!(bs.length == word_to_nat count)) = true
                  · rw [ite_eq_left hfull] at Hs ⊢
                    try rfl
                  · rw [ite_eq_right hfull] at Hs ⊢
                    try dsimp only at Hs ⊢
                    exact absurd Hs
                      (seqSpec_set_pipes_record_ret_only_no_unmodeled _ _ _ i m)
    | FdDevNull rd wr =>
      try dsimp only at Hs ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at Hs ⊢
        cases Hs
      · rw [ite_eq_right hwr] at Hs ⊢
        by_cases hmr : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left hmr] at Hs ⊢
          try rfl
        · rw [ite_eq_right hmr] at Hs ⊢
          ok_zsplit_c Hs buf count
          · exact absurd Hs (pure_no_unmodeled _ i m)
          · cases Hs
    | FdUrandom =>
      try dsimp only at Hs ⊢
      cases Hs

end LinuxSem.Checks.Sys.Fs.ReadWrite
