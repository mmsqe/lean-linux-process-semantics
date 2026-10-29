/-
  * LinuxProcessSem.Checks.Sys.Fs.ReadWrite.Readv — the `readv` (65)
    checker's soundness and completeness

  The four `check_readv_*` lemmas — `check_readv_sound_ok`,
  `check_readv_sound_unmodeled`, `check_readv_complete_ok` and
  `check_readv_complete_unmodeled` — split out of the parent module so that
  it stops growing; with this file and `ReadWrite/Write.lean` and
  `ReadWrite/Vec.lean`, the parent's whole lemma set is in the tree.

  The statements are the parent's `readv_spec` / `check_readv` verbatim.
  `check_readv` is the composition of `check_readv_imported` (the
  imported-vector body, whose gap arms decline) with the iovec import and
  the copy-in ledger, so this file also carries the four
  `check_readv_imported_*` lemmas those proofs invert.  They are PRIVATE
  here: `Checks/Sys/Fs/ReadWrite/Vec.lean` is where the public copies of
  `check_readv_imported_{sound_ok,sound_unmodeled,complete_ok,
  complete_unmodeled}` belong, and a second public copy in the same
  namespace could not coexist with it.  Nothing here depends on that file:
  this module verifies against the parent alone.

  The helpers below carry the delivery's write ledger left general (the
  parent's `seqSpec_set_{stdin,fds}_deliver_ok` spell it `[(buf, bs)]`,
  which is the scalar `read`'s shape, not `readv`'s).
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

/- =========================================================================
   The delivery stages, with the ledger left general

   The parent's `seqSpec_set_stdin_deliver_ok` / `seqSpec_set_fds_deliver_ok`
   state the delivery of a SCALAR read — one `(buf, bs)` write.  A readv
   scatters the same bytes across the imported vector, so the ledger is the
   checker's `scatter_iovecs` result; these two state exactly that, and
   their inverses are what the completeness directions take apart.
   ========================================================================= -/

/-- The channel delivery stage at an arbitrary ledger. -/
private theorem rv_stdin_deliver_ok (stdin : InputStream) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput) (m : Model) :
    seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m
      (.ok (mkEffect (len_word bs) writes []) (with_stdin stdin m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_stdin stdin m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_stdin stdin m, bs.map (event.ReadEv ch), [], rfl, rfl, ?_⟩
  simp

/-- The socket delivery stage at an arbitrary ledger. -/
private theorem rv_fds_deliver_ok (fds : List (word × FdEntry)) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m
      (.ok (mkEffect (len_word bs) writes []) (with_fds fds m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_fds fds m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_fds fds m, bs.map (event.ReadEv ch), [], rfl, rfl, ?_⟩
  simp

/-- Invert the channel delivery stage. -/
private theorem rv_stdin_deliver_ok_inv (stdin : InputStream) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) writes []
      ∧ m' = with_stdin stdin m ∧ evs = bs.map (event.ReadEv ch) := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_stdin, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨y, m2, ev3, ev4, h4, h5, h6⟩ := h2
  cases h4
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/-- Invert the socket delivery stage. -/
private theorem rv_fds_deliver_ok_inv (fds : List (word × FdEntry)) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) writes []
      ∧ m' = with_fds fds m ∧ evs = bs.map (event.ReadEv ch) := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  simp only [set_fds, modifySpec, LinuxSem.LinuxProcessSem.modify] at h1
  cases h1
  obtain ⟨y, m2, ev3, ev4, h4, h5, h6⟩ := h2
  cases h4
  cases h5
  simp only [List.nil_append, List.append_nil] at h3 h6
  cases h6
  cases h3
  exact ⟨rfl, rfl, rfl⟩

/-- The delivered-prefix guard of a channel readv, at the
    spec's `choose` witness (`ret = len_word bs`, ledger = the canonical
    scatter of `bs`). -/
private theorem rv_guard_true (m : Model) (total : Int)
    (writes : List (word × List byte)) (bs : List byte)
    (h1 : 1 ≤ (bs.length : Int))
    (h2 : (bs.length : Int) ≤ total)
    (htake : (stream_take (m_stdin m) bs.length).1 = bs) :
    (bv_eqb (len_word bs) (len_word bs) && writes_eqb writes writes
      && decide (1 ≤ (bs.length : Int))
      && decide ((bs.length : Int) ≤ total)
      && listN_eqb (stream_take (m_stdin m) bs.length).1 bs) = true := by
  simp only [bv_eqb_refl, (writes_eqb_eq _ _).mpr rfl, decide_eq_true h1,
    decide_eq_true h2, (listN_eqb_eq _ _).mpr htake, Bool.and_true]

/-- The same guard on a socket, over the connection's script. -/
private theorem rv_socket_guard_true (total : Int)
    (rx : NetStream) (writes : List (word × List byte)) (bs : List byte)
    (h1 : 1 ≤ (bs.length : Int))
    (h2 : (bs.length : Int) ≤ total)
    (htake : (net_take rx bs.length).1 = bs) :
    (bv_eqb (len_word bs) (len_word bs) && writes_eqb writes writes
      && decide (1 ≤ (bs.length : Int))
      && decide ((bs.length : Int) ≤ total)
      && listN_eqb (net_take rx bs.length).1 bs) = true := by
  simp only [bv_eqb_refl, (writes_eqb_eq _ _).mpr rfl, decide_eq_true h1,
    decide_eq_true h2, (listN_eqb_eq _ _).mpr htake, Bool.and_true]

/- =========================================================================
   check_readv_imported — the imported-vector body (PRIVATE; see the header)
   ========================================================================= -/

/-- `check_readv_imported` accepted implies `readv_imported`.  The two arms that
    deliver (a channel and a connected socket with a live script) build the
    spec's `choose` witness out of the ledger the checker accepted: the
    delivered bytes are its flattened writes, and `scatter_iovecs_concat`
    is what ties them back to the checker's own `bs`. -/
private theorem readv_imported_sound_ok (i : SyscallInput) (fd : word)
    (r : ReadableFd) (iovs0 : List (word × word)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_readv_imported i fd r iovs0 eff m = .CheckOk m' evs) :
    readv_imported fd r iovs0 i m i m (.ok eff m' evs) := by
  unfold check_readv_imported at H
  unfold readv_imported
  dsimp only at H ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs0) == 0) = true
  · rw [ite_eq_left hz] at H ⊢
    exact ret_only_ok_spec H i
  · rw [ite_eq_right hz] at H ⊢
    generalize hr : r = rr at H ⊢
    cases rr with
    | RdChannel ch =>
      dsimp only at H ⊢
      generalize hs : m_stdin m 0 = st at H ⊢
      cases st with
      | none =>
        dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | some b0 =>
        dsimp only at H ⊢
        generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
          [BitVec.ofInt 8 0] = s1 at H ⊢
        cases s1 with
        | none =>
          dsimp only at H ⊢
          exact ret_only_ok_spec H i
        | some w1 =>
          dsimp only at H ⊢
          generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = s2 at H ⊢
          cases s2 with
          | none =>
            dsimp only at H ⊢
            unfold check_readv_gap at H
            exact nomatch H
          | some w2 =>
            dsimp only at H ⊢
            obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
            cases zs with
            | nil =>
              cases us with
              | nil =>
                cases cs with
                | nil =>
                  cases ks with
                  | nil =>
                    try dsimp only at H ⊢
                    generalize hbs : (ws.map Prod.snd).flatten = bs at H ⊢
                    try dsimp only at H ⊢
                    generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc
                      at H ⊢
                    cases sc with
                    | none => try dsimp only at H; exact nomatch H
                    | some expected =>
                      try dsimp only at H ⊢
                      by_cases hg : (bv_eqb ret (len_word bs) && writes_eqb ws expected
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0))
                          && listN_eqb (stream_take (m_stdin m) bs.length).1 bs) = true
                      · rw [ite_eq_left hg] at H
                        cases H
                        have hg' : bv_eqb ret (len_word bs) = true
                            ∧ writes_eqb ws expected = true
                            ∧ decide (1 ≤ (bs.length : Int)) = true
                            ∧ decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0)) = true
                            ∧ listN_eqb (stream_take (m_stdin m) bs.length).1 bs = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hg
                        obtain ⟨hret, hws, hle1, hle2, htake⟩ := hg'
                        have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret _).mp hret
                        have hws' : ws = expected := (writes_eqb_eq ws expected).mp hws
                        refine ⟨bs, m, [], bs.map (event.ReadEv ch),
                          choose_ok _ bs i m ⟨?_, ?_, ?_, ?_⟩, ?_, rfl⟩
                        · exact of_decide_eq_true hle1
                        · exact of_decide_eq_true hle2
                        · exact (listN_eqb_eq _ _).mp htake
                        · rw [hsc]; simp
                        · rw [hret', hws']
                          dsimp only
                          rw [hsc]
                          exact rv_stdin_deliver_ok _ ch expected bs i m
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
            | cons _ _ => try dsimp only at H; exact nomatch H
    | RdFile p off =>
      dsimp only at H ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at H ⊢
      cases fsl with
      | none =>
        dsimp only at H ⊢
        unfold check_readv_gap at H
        exact nomatch H
      | some data =>
        dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at H ⊢
          cases sc with
          | none =>
            dsimp only at H ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at H ⊢
            cases s1 with
            | none =>
              dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some w1 =>
              dsimp only at H ⊢
              unfold check_readv_gap at H
              exact nomatch H
          | some writes =>
            dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at H
              unfold check_readv_gap at H
              exact nomatch H
            · rw [ite_eq_right hae] at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases ks with
                    | nil =>
                      try dsimp only at H ⊢
                      by_cases hg : (bv_eqb ret (len_word bs)
                          && writes_eqb ws writes) = true
                      · rw [ite_eq_left hg] at H
                        cases H
                        have hg' : bv_eqb ret (len_word bs) = true
                            ∧ writes_eqb ws writes = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hg
                        obtain ⟨hret, hws⟩ := hg'
                        have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret _).mp hret
                        have hws' : ws = writes := (writes_eqb_eq ws writes).mp hws
                        rw [hret', hws']
                        exact seqSpec_set_fds_pure_ok _ (mkEffect (len_word bs) writes []) i m
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
    | RdFileRW p off =>
      dsimp only at H ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at H ⊢
      cases fsl with
      | none =>
        dsimp only at H ⊢
        unfold check_readv_gap at H
        exact nomatch H
      | some data =>
        dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at H ⊢
          cases sc with
          | none =>
            dsimp only at H ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at H ⊢
            cases s1 with
            | none =>
              dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some w1 =>
              dsimp only at H ⊢
              unfold check_readv_gap at H
              exact nomatch H
          | some writes =>
            dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at H
              unfold check_readv_gap at H
              exact nomatch H
            · rw [ite_eq_right hae] at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases ks with
                    | nil =>
                      try dsimp only at H ⊢
                      by_cases hg : (bv_eqb ret (len_word bs)
                          && writes_eqb ws writes) = true
                      · rw [ite_eq_left hg] at H
                        cases H
                        have hg' : bv_eqb ret (len_word bs) = true
                            ∧ writes_eqb ws writes = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hg
                        obtain ⟨hret, hws⟩ := hg'
                        have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret _).mp hret
                        have hws' : ws = writes := (writes_eqb_eq ws writes).mp hws
                        rw [hret', hws']
                        exact seqSpec_set_fds_pure_ok _ (mkEffect (len_word bs) writes []) i m
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
    | RdDir =>
      dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | RdSocket sk =>
      dsimp only at H ⊢
      generalize hsk : sk = sk' at H ⊢
      cases sk' with
      | SkFresh =>
        dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | SkBound =>
        dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | SkListening =>
        dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | SkConnected peer ch rx =>
        dsimp only at H ⊢
        generalize hrx : rx 0 = nx at H ⊢
        cases nx with
        | fin =>
          dsimp only at H ⊢
          exact ret_only_ok_spec H i
        | rst =>
          dsimp only at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret ECONNRESET)
              (with_fds (fd_insert (m_fds m) fd
                (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [] m' evs).mp H
          exact seqSpec_set_fds_err_ret_ok _ ECONNRESET i m
        | timedOut =>
          dsimp only at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret ETIMEDOUT)
              (with_fds (fd_insert (m_fds m) fd
                (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [] m' evs).mp H
          exact seqSpec_set_fds_err_ret_ok _ ETIMEDOUT i m
        | cons b0 =>
          dsimp only at H ⊢
          generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            [BitVec.ofInt 8 0] = s1 at H ⊢
          cases s1 with
          | none =>
            dsimp only at H ⊢
            exact ret_only_ok_spec H i
          | some w1 =>
            dsimp only at H ⊢
            generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = s2 at H ⊢
            cases s2 with
            | none =>
              dsimp only at H ⊢
              unfold check_readv_gap at H
              exact nomatch H
            | some w2 =>
              dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases ks with
                    | nil =>
                      try dsimp only at H ⊢
                      generalize hbs : (ws.map Prod.snd).flatten = bs at H ⊢
                      try dsimp only at H ⊢
                      generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc
                        at H ⊢
                      cases sc with
                      | none => try dsimp only at H; exact nomatch H
                      | some expected =>
                        try dsimp only at H ⊢
                        by_cases hg : (bv_eqb ret (len_word bs) && writes_eqb ws expected
                            && decide (1 ≤ (bs.length : Int))
                            && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0))
                            && listN_eqb (net_take rx bs.length).1 bs) = true
                        · rw [ite_eq_left hg] at H
                          cases H
                          have hg' : bv_eqb ret (len_word bs) = true
                              ∧ writes_eqb ws expected = true
                              ∧ decide (1 ≤ (bs.length : Int)) = true
                              ∧ decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0)) = true
                              ∧ listN_eqb (net_take rx bs.length).1 bs = true := by
                            simpa [Bool.and_eq_true, and_assoc] using hg
                          obtain ⟨hret, hws, hle1, hle2, htake⟩ := hg'
                          have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret _).mp hret
                          have hws' : ws = expected := (writes_eqb_eq ws expected).mp hws
                          refine ⟨bs, m, [], bs.map (event.ReadEv ch),
                            choose_ok _ bs i m ⟨?_, ?_, ?_, ?_⟩, ?_, rfl⟩
                          · exact of_decide_eq_true hle1
                          · exact of_decide_eq_true hle2
                          · exact (listN_eqb_eq _ _).mp htake
                          · rw [hsc]; simp
                          · rw [hret', hws']
                            dsimp only
                            rw [hsc]
                            exact rv_fds_deliver_ok _ ch expected bs i m
                        · rw [ite_eq_right hg] at H
                          exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
      | SkReset peer ch =>
        dsimp only at H ⊢
        exact ret_only_ok_spec H i
    | RdPipe id =>
      dsimp only at H ⊢
      unfold check_readv_gap at H
      exact nomatch H
    | RdDevNull =>
      dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | RdUrandom =>
      dsimp only at H ⊢
      unfold check_readv_gap at H
      exact nomatch H


/-- `check_readv_imported` declining implies `readv_imported` declining. -/
private theorem readv_imported_sound_unmodeled (i : SyscallInput) (fd : word)
    (r : ReadableFd) (iovs0 : List (word × word)) (eff : SyscallEffect) (m : Model)
    (H : check_readv_imported i fd r iovs0 eff m = .CheckUnmodeled) :
    readv_imported fd r iovs0 i m i m .unmodeled := by
  unfold check_readv_imported at H
  unfold readv_imported
  dsimp only at H ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs0) == 0) = true
  · rw [ite_eq_left hz] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
  · rw [ite_eq_right hz] at H ⊢
    generalize hr : r = rr at H ⊢
    cases rr with
    | RdChannel ch =>
      dsimp only at H ⊢
      generalize hs : m_stdin m 0 = st at H ⊢
      cases st with
      | none =>
        dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      | some b0 =>
        dsimp only at H ⊢
        generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
          [BitVec.ofInt 8 0] = s1 at H ⊢
        cases s1 with
        | none =>
          dsimp only at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        | some w1 =>
          dsimp only at H ⊢
          generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = s2 at H ⊢
          cases s2 with
          | none =>
            dsimp only at H ⊢
            unfold readv_buf_gap
            exact unmodeled_intro i m
          | some w2 =>
            dsimp only at H ⊢
            obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
            cases zs with
            | nil =>
              cases us with
              | nil =>
                cases cs with
                | nil =>
                  cases ks with
                  | nil =>
                    try dsimp only at H
                    generalize hbs : (ws.map Prod.snd).flatten = bs at H
                    try dsimp only at H
                    generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc
                      at H
                    cases sc with
                    | none => exact nomatch H
                    | some expected =>
                      try dsimp only at H
                      by_cases hg : (bv_eqb ret (len_word bs) && writes_eqb ws expected
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0))
                          && listN_eqb (stream_take (m_stdin m) bs.length).1 bs) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
            | cons _ _ => try dsimp only at H; exact nomatch H
    | RdFile p off =>
      dsimp only at H ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at H ⊢
      cases fsl with
      | none =>
        dsimp only at H ⊢
        unfold readv_buf_gap
        exact unmodeled_intro i m
      | some data =>
        dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at H ⊢
          cases sc with
          | none =>
            dsimp only at H ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at H ⊢
            cases s1 with
            | none =>
              dsimp only at H ⊢
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | some w1 =>
              dsimp only at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
          | some writes =>
            dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
            · rw [ite_eq_right hae] at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases ks with
                    | nil =>
                      try dsimp only at H
                      by_cases hg : (bv_eqb ret (len_word bs)
                          && writes_eqb ws writes) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
    | RdFileRW p off =>
      dsimp only at H ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at H ⊢
      cases fsl with
      | none =>
        dsimp only at H ⊢
        unfold readv_buf_gap
        exact unmodeled_intro i m
      | some data =>
        dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at H ⊢
          cases sc with
          | none =>
            dsimp only at H ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at H ⊢
            cases s1 with
            | none =>
              dsimp only at H ⊢
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | some w1 =>
              dsimp only at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
          | some writes =>
            dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
            · rw [ite_eq_right hae] at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases ks with
                    | nil =>
                      try dsimp only at H
                      by_cases hg : (bv_eqb ret (len_word bs)
                          && writes_eqb ws writes) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
    | RdDir =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
    | RdSocket sk =>
      dsimp only at H ⊢
      generalize hsk : sk = sk' at H ⊢
      cases sk' with
      | SkFresh =>
        dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
      | SkBound =>
        dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
      | SkListening =>
        dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
      | SkConnected peer ch rx =>
        dsimp only at H ⊢
        generalize hrx : rx 0 = nx at H ⊢
        cases nx with
        | fin =>
          dsimp only at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
        | rst =>
          dsimp only at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ECONNRESET)
            (with_fds (fd_insert (m_fds m) fd
              (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])
        | timedOut =>
          dsimp only at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ETIMEDOUT)
            (with_fds (fd_insert (m_fds m) fd
              (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])
        | cons b0 =>
          dsimp only at H ⊢
          generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            [BitVec.ofInt 8 0] = s1 at H ⊢
          cases s1 with
          | none =>
            dsimp only at H ⊢
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          | some w1 =>
            dsimp only at H ⊢
            generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = s2 at H ⊢
            cases s2 with
            | none =>
              dsimp only at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
            | some w2 =>
              dsimp only at H ⊢
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases ks with
                    | nil =>
                      try dsimp only at H
                      generalize hbs : (ws.map Prod.snd).flatten = bs at H
                      try dsimp only at H
                      generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc
                        at H
                      cases sc with
                      | none => exact nomatch H
                      | some expected =>
                        try dsimp only at H
                        by_cases hg : (bv_eqb ret (len_word bs) && writes_eqb ws expected
                            && decide (1 ≤ (bs.length : Int))
                            && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs0))
                            && listN_eqb (net_take rx bs.length).1 bs) = true
                        · rw [ite_eq_left hg] at H
                          exact nomatch H
                        · rw [ite_eq_right hg] at H
                          exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
              | cons _ _ => try dsimp only at H; exact nomatch H
      | SkReset peer ch =>
        dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | RdPipe id =>
      dsimp only at H ⊢
      unfold readv_buf_gap
      exact unmodeled_intro i m
    | RdDevNull =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | RdUrandom =>
      dsimp only at H ⊢
      unfold readv_buf_gap
      exact unmodeled_intro i m

/-- `readv_imported` accepted implies `check_readv_imported` accepts it.
   The
    two delivering arms invert the spec's `choose` with
    [choose_bind_ok_inv], and `scatter_iovecs_concat` turns the accepted
    ledger back into the checker's own `bs`. -/
private theorem readv_imported_complete_ok (i : SyscallInput) (fd : word)
    (r : ReadableFd) (iovs0 : List (word × word)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (Hs : readv_imported fd r iovs0 i m i m (.ok eff m' evs)) :
    check_readv_imported i fd r iovs0 eff m = .CheckOk m' evs := by
  unfold readv_imported at Hs
  simp only [check_readv_imported]
  dsimp only at Hs ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs0) == 0) = true
  · rw [ite_eq_left hz] at Hs ⊢
    cases Hs
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hz] at Hs ⊢
    generalize hr : r = rr at Hs ⊢
    cases rr with
    | RdChannel ch =>
      dsimp only at Hs ⊢
      generalize hs : m_stdin m 0 = st at Hs ⊢
      cases st with
      | none =>
        dsimp only at Hs ⊢
        cases Hs
        simp [check_ret_only, bv_eqb_refl]
      | some b0 =>
        dsimp only at Hs ⊢
        generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
          [BitVec.ofInt 8 0] = s1 at Hs ⊢
        cases s1 with
        | none =>
          dsimp only at Hs ⊢
          cases Hs
          simp [check_ret_only, bv_eqb_refl]
        | some w1 =>
          dsimp only at Hs ⊢
          generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = s2 at Hs ⊢
          cases s2 with
          | none =>
            dsimp only at Hs ⊢
            unfold readv_buf_gap at Hs
            exact nomatch Hs
          | some w2 =>
            obtain ⟨bs, hP, Hk⟩ := choose_bind_ok_inv _ _ i m eff m' evs Hs
            obtain ⟨h1, h2, htake, hne⟩ := hP
            cases hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs with
            | none =>
              simp only [hsc] at Hk
              rcases Hk with ⟨x, hf, -⟩
              exact hf.elim
            | some writes =>
              simp only [hsc] at Hk
              obtain ⟨heff, hm', hevs⟩ :=
                rv_stdin_deliver_ok_inv _ ch writes bs i m eff m' evs Hk
              subst heff
              subst hm'
              subst hevs
              try dsimp only
              rw [scatter_iovecs_concat _ _ _ _ hsc]
              rw [hsc]
              try dsimp only
              rw [rv_guard_true m (iovs_total (cap_iovecs iovs0)) writes bs h1 h2 htake]
              simp
    | RdFile p off =>
      dsimp only at Hs ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at Hs ⊢
      cases fsl with
      | none =>
        dsimp only at Hs ⊢
        unfold readv_buf_gap at Hs
        exact nomatch Hs
      | some data =>
        dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          cases Hs
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at Hs ⊢
          cases sc with
          | none =>
            dsimp only at Hs ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at Hs ⊢
            cases s1 with
            | none =>
              dsimp only at Hs ⊢
              cases Hs
              simp [check_ret_only, bv_eqb_refl]
            | some w1 =>
              dsimp only at Hs ⊢
              unfold readv_buf_gap at Hs
              exact nomatch Hs
          | some writes =>
            dsimp only at Hs ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at Hs ⊢
              unfold readv_buf_gap at Hs
              exact nomatch Hs
            · rw [ite_eq_right hae] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word bs) writes []) i m eff m' evs Hs
              subst heff
              subst hm'
              subst hevs
              try dsimp only
              rw [show (bv_eqb (len_word bs) (len_word bs)
                  && writes_eqb writes writes) = true from by
                simp only [bv_eqb_refl, (writes_eqb_eq _ _).mpr rfl, Bool.and_true]]
              simp
    | RdFileRW p off =>
      dsimp only at Hs ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at Hs ⊢
      cases fsl with
      | none =>
        dsimp only at Hs ⊢
        unfold readv_buf_gap at Hs
        exact nomatch Hs
      | some data =>
        dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          cases Hs
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at Hs ⊢
          cases sc with
          | none =>
            dsimp only at Hs ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at Hs ⊢
            cases s1 with
            | none =>
              dsimp only at Hs ⊢
              cases Hs
              simp [check_ret_only, bv_eqb_refl]
            | some w1 =>
              dsimp only at Hs ⊢
              unfold readv_buf_gap at Hs
              exact nomatch Hs
          | some writes =>
            dsimp only at Hs ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at Hs ⊢
              unfold readv_buf_gap at Hs
              exact nomatch Hs
            · rw [ite_eq_right hae] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word bs) writes []) i m eff m' evs Hs
              subst heff
              subst hm'
              subst hevs
              try dsimp only
              rw [show (bv_eqb (len_word bs) (len_word bs)
                  && writes_eqb writes writes) = true from by
                simp only [bv_eqb_refl, (writes_eqb_eq _ _).mpr rfl, Bool.and_true]]
              simp
    | RdDir =>
      dsimp only at Hs ⊢
      cases Hs
      simp [check_ret_only, bv_eqb_refl]
    | RdSocket sk =>
      dsimp only at Hs ⊢
      generalize hsk : sk = sk' at Hs ⊢
      cases sk' with
      | SkFresh =>
        dsimp only at Hs ⊢
        cases Hs
        simp [check_ret_only, bv_eqb_refl]
      | SkBound =>
        dsimp only at Hs ⊢
        cases Hs
        simp [check_ret_only, bv_eqb_refl]
      | SkListening =>
        dsimp only at Hs ⊢
        cases Hs
        simp [check_ret_only, bv_eqb_refl]
      | SkConnected peer ch rx =>
        dsimp only at Hs ⊢
        generalize hrx : rx 0 = nx at Hs ⊢
        cases nx with
        | fin =>
          dsimp only at Hs ⊢
          cases Hs
          simp [check_ret_only, bv_eqb_refl]
        | rst =>
          dsimp only at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            seqSpec_set_fds_err_ret_ok_inv _ ECONNRESET i m eff m' evs Hs
          subst heff
          subst hm'
          subst hevs
          simp [check_ret_only, bv_eqb_refl]
        | timedOut =>
          dsimp only at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            seqSpec_set_fds_err_ret_ok_inv _ ETIMEDOUT i m eff m' evs Hs
          subst heff
          subst hm'
          subst hevs
          simp [check_ret_only, bv_eqb_refl]
        | cons b0 =>
          dsimp only at Hs ⊢
          generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            [BitVec.ofInt 8 0] = s1 at Hs ⊢
          cases s1 with
          | none =>
            dsimp only at Hs ⊢
            cases Hs
            simp [check_ret_only, bv_eqb_refl]
          | some w1 =>
            dsimp only at Hs ⊢
            generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = s2 at Hs ⊢
            cases s2 with
            | none =>
              dsimp only at Hs ⊢
              unfold readv_buf_gap at Hs
              exact nomatch Hs
            | some w2 =>
              obtain ⟨bs, hP, Hk⟩ := choose_bind_ok_inv _ _ i m eff m' evs Hs
              obtain ⟨h1, h2, htake, hne⟩ := hP
              cases hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs with
              | none =>
                simp only [hsc] at Hk
                rcases Hk with ⟨x, hf, -⟩
                exact hf.elim
              | some writes =>
                simp only [hsc] at Hk
                obtain ⟨heff, hm', hevs⟩ :=
                  rv_fds_deliver_ok_inv _ ch writes bs i m eff m' evs Hk
                subst heff
                subst hm'
                subst hevs
                try dsimp only
                rw [scatter_iovecs_concat _ _ _ _ hsc]
                rw [hsc]
                try dsimp only
                rw [rv_socket_guard_true (iovs_total (cap_iovecs iovs0)) rx writes bs
                  h1 h2 htake]
                simp
      | SkReset peer ch =>
        dsimp only at Hs ⊢
        cases Hs
        simp [check_ret_only, bv_eqb_refl]
    | RdPipe id =>
      dsimp only at Hs ⊢
      unfold readv_buf_gap at Hs
      exact nomatch Hs
    | RdDevNull =>
      dsimp only at Hs ⊢
      cases Hs
      simp [check_ret_only, bv_eqb_refl]
    | RdUrandom =>
      dsimp only at Hs ⊢
      unfold readv_buf_gap at Hs
      exact nomatch Hs

/-- `readv_imported` declining implies `check_readv_imported` declines.

    In the two delivering arms the spec CANNOT decline —
    [choose_bind_no_unmodeled] with [deliverSeq_no_unmodeled] — so those
    arms are refuted from `Hs` rather than walked; the model-scattered gap
    arms are the only ones where both sides decline, and they are `rfl`. -/
private theorem readv_imported_complete_unmodeled (i : SyscallInput) (fd : word)
    (r : ReadableFd) (iovs0 : List (word × word)) (m : Model) (eff : SyscallEffect)
    (Hs : readv_imported fd r iovs0 i m i m .unmodeled) :
    check_readv_imported i fd r iovs0 eff m = .CheckUnmodeled := by
  unfold readv_imported at Hs
  simp only [check_readv_imported]
  dsimp only at Hs ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs0) == 0) = true
  · rw [ite_eq_left hz] at Hs ⊢
    exact absurd Hs (pure_no_unmodeled _ i m)
  · rw [ite_eq_right hz] at Hs ⊢
    generalize hr : r = rr at Hs ⊢
    cases rr with
    | RdChannel ch =>
      dsimp only at Hs ⊢
      generalize hs : m_stdin m 0 = st at Hs ⊢
      cases st with
      | none =>
        dsimp only at Hs ⊢
        exact absurd Hs (pure_no_unmodeled _ i m)
      | some b0 =>
        dsimp only at Hs ⊢
        generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
          [BitVec.ofInt 8 0] = s1 at Hs ⊢
        cases s1 with
        | none =>
          dsimp only at Hs ⊢
          exact absurd Hs (pure_no_unmodeled _ i m)
        | some w1 =>
          dsimp only at Hs ⊢
          generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs0))).1 = s2 at Hs ⊢
          cases s2 with
          | none =>
            dsimp only at Hs ⊢
            unfold check_readv_gap
            rfl
          | some w2 =>
            dsimp only at Hs ⊢
            exfalso
            refine absurd Hs (choose_bind_no_unmodeled _ _ i m ?_)
            intro a
            cases hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) a with
            | none => exact choose_no_unmodeled _ i m
            | some w => exact deliverSeq_no_unmodeled _ _ _ i m
    | RdFile p off =>
      dsimp only at Hs ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at Hs ⊢
      cases fsl with
      | none =>
        dsimp only at Hs ⊢
        unfold check_readv_gap
        rfl
      | some data =>
        dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          exact absurd Hs (pure_no_unmodeled _ i m)
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at Hs ⊢
          cases sc with
          | none =>
            dsimp only at Hs ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at Hs ⊢
            cases s1 with
            | none =>
              dsimp only at Hs ⊢
              exact absurd Hs (pure_no_unmodeled _ i m)
            | some w1 =>
              dsimp only at Hs ⊢
              unfold check_readv_gap
              rfl
          | some writes =>
            dsimp only at Hs ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at Hs ⊢
              unfold check_readv_gap
              rfl
            · rw [ite_eq_right hae] at Hs ⊢
              exact absurd Hs
                (seqSpec_pure_no_unmodeled _ _ i m (modifySpec_no_unmodeled _ i m))
    | RdFileRW p off =>
      dsimp only at Hs ⊢
      generalize hfs : Fs.fs_lookup (m_fs m) p = fsl at Hs ⊢
      cases fsl with
      | none =>
        dsimp only at Hs ⊢
        unfold check_readv_gap
        rfl
      | some data =>
        dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          exact absurd Hs (pure_no_unmodeled _ i m)
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hb : Fs.file_read data off
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at Hs ⊢
          cases sc with
          | none =>
            dsimp only at Hs ⊢
            generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              [BitVec.ofInt 8 0] = s1 at Hs ⊢
            cases s1 with
            | none =>
              dsimp only at Hs ⊢
              exact absurd Hs (pure_no_unmodeled _ i m)
            | some w1 =>
              dsimp only at Hs ⊢
              unfold check_readv_gap
              rfl
          | some writes =>
            dsimp only at Hs ⊢
            by_cases hae : addr_is_error_b (len_word bs) = true
            · rw [ite_eq_left hae] at Hs ⊢
              unfold check_readv_gap
              rfl
            · rw [ite_eq_right hae] at Hs ⊢
              exact absurd Hs
                (seqSpec_pure_no_unmodeled _ _ i m (modifySpec_no_unmodeled _ i m))
    | RdDir =>
      dsimp only at Hs ⊢
      exact absurd Hs (pure_no_unmodeled _ i m)
    | RdSocket sk =>
      dsimp only at Hs ⊢
      generalize hsk : sk = sk' at Hs ⊢
      cases sk' with
      | SkFresh =>
        dsimp only at Hs ⊢
        exact absurd Hs (pure_no_unmodeled _ i m)
      | SkBound =>
        dsimp only at Hs ⊢
        exact absurd Hs (pure_no_unmodeled _ i m)
      | SkListening =>
        dsimp only at Hs ⊢
        exact absurd Hs (pure_no_unmodeled _ i m)
      | SkConnected peer ch rx =>
        dsimp only at Hs ⊢
        generalize hrx : rx 0 = nx at Hs ⊢
        cases nx with
        | fin =>
          dsimp only at Hs ⊢
          exact absurd Hs (pure_no_unmodeled _ i m)
        | rst =>
          dsimp only at Hs ⊢
          exact absurd Hs
            (seqSpec_pure_no_unmodeled _ _ i m (modifySpec_no_unmodeled _ i m))
        | timedOut =>
          dsimp only at Hs ⊢
          exact absurd Hs
            (seqSpec_pure_no_unmodeled _ _ i m (modifySpec_no_unmodeled _ i m))
        | cons b0 =>
          dsimp only at Hs ⊢
          generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
            [BitVec.ofInt 8 0] = s1 at Hs ⊢
          cases s1 with
          | none =>
            dsimp only at Hs ⊢
            exact absurd Hs (pure_no_unmodeled _ i m)
          | some w1 =>
            dsimp only at Hs ⊢
            generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
              (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = s2 at Hs ⊢
            cases s2 with
            | none =>
              dsimp only at Hs ⊢
              unfold check_readv_gap
              rfl
            | some w2 =>
              dsimp only at Hs ⊢
              exfalso
              refine absurd Hs (choose_bind_no_unmodeled _ _ i m ?_)
              intro a
              cases hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) a with
              | none => exact choose_no_unmodeled _ i m
              | some w => exact deliverSeq_no_unmodeled _ _ _ i m
      | SkReset peer ch =>
        dsimp only at Hs ⊢
        exact absurd Hs (pure_no_unmodeled _ i m)
    | RdPipe id =>
      dsimp only at Hs ⊢
      unfold check_readv_gap
      rfl
    | RdDevNull =>
      dsimp only at Hs ⊢
      exact absurd Hs (pure_no_unmodeled _ i m)
    | RdUrandom =>
      dsimp only at Hs ⊢
      unfold check_readv_gap
      rfl


/- =========================================================================
   readv (65) — the four lemmas of the assignment
   ========================================================================= -/

/-- An errno leaf of `readv_spec`'s iovec-reading stage.  The parent's
    `check_pwrite64_sound_ok` takes the same step per arm. -/
private theorem rv_errno_leaf (i : SyscallInput) (reads : List (word × Nat))
    (e : Int) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ret_only_copyins reads eff (errno_ret e) m [] = .CheckOk m' evs) :
    record_copyins reads
      (LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret e) i m
      (.ok eff m' evs) := by
  obtain ⟨heff, hm', hevs⟩ :=
    (check_ret_only_copyins_ok_iff reads eff (errno_ret e) m [] m' evs).mp H
  subst heff
  subst hm'
  subst hevs
  exact record_copyins_ok_empty (reads := reads) rfl (pure_ok _ i _)

/-- `check_readv` accepted implies `readv_spec`.  That stage hands the
    imported-vector body an effect with the descriptor ranges STRIPPED off
    its ledger; [record_copyins_clear_ok] cannot be used for that (it wants
    the ledger clear, not a prefix), so the ledger is rebuilt with
    `record_copyins_ok` after `List.take_append_drop` reconstitutes the
    accepted prefix. -/
theorem check_readv_sound_ok (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_readv i fd iov iovcnt eff m = .CheckOk m' evs) :
    readv_spec fd iov iovcnt i m (.ok eff m' evs) := by
  unfold readv_spec
  simp only [check_readv] at H
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
    try dsimp only at H ⊢
    generalize hr : readable_fd e = rr at H ⊢
    cases rr with
    | none =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | some r =>
      try dsimp only at H ⊢
      by_cases hheap : readv_heap_iovecb iovcnt = true
      · rw [ite_eq_left hheap] at H ⊢
        unfold check_readv_gap at H
        exact nomatch H
      · rw [ite_eq_right hheap] at H ⊢
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at H ⊢
        cases imp with
        | ImpFault =>
          try dsimp only at H ⊢
          exact rv_errno_leaf i _ EFAULT eff m m' evs H
        | ImpInval =>
          try dsimp only at H ⊢
          exact rv_errno_leaf i _ EINVAL eff m m' evs H
        | ImpOk iovs0 =>
          try dsimp only at H ⊢
          unfold check_copyin_prefix at H
          generalize hc : check_readv_imported i fd r iovs0
            (strip_copyin_prefix (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff) m
            = cres at H
          cases cres with
          | CheckUnmodeled =>
            try dsimp only at H
            exact nomatch H
          | CheckReject =>
            try dsimp only at H
            by_cases hreads : access_ranges_eqb
              (eff.eff_copyins.take (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length)
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) = true
            · simp [hreads] at H
            · simp [hreads] at H
          | CheckOk m'' evs'' =>
            try dsimp only at H
            by_cases hreads : access_ranges_eqb
              (eff.eff_copyins.take (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length)
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) = true
            · rw [ite_eq_left hreads] at H
              cases H
              have hreads' : eff.eff_copyins.take
                  (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length
                  = import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) :=
                (access_ranges_eqb_eq _ _).mp hreads
              have hcopy : import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                  eff.eff_copyins.drop
                    (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length
                  = eff.eff_copyins := by
                calc import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                      eff.eff_copyins.drop
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length
                    = eff.eff_copyins.take
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length ++
                      eff.eff_copyins.drop
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length := by
                        rw [hreads']
                  _ = eff.eff_copyins := List.take_append_drop _ _
              have heffeq : with_copyins
                    (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                     (strip_copyin_prefix
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff).eff_copyins)
                    (strip_copyin_prefix
                       (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff)
                  = eff := by
                simp only [strip_copyin_prefix, with_copyins, hcopy]
              rw [← heffeq]
              exact record_copyins_ok
                (readv_imported_sound_ok i fd r iovs0 _ m _ _ hc)
            · simp [hreads] at H

/-- `check_readv` declining implies `readv_spec` declining -/
theorem check_readv_sound_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_readv i fd iov iovcnt eff m = .CheckUnmodeled) :
    readv_spec fd iov iovcnt i m .unmodeled := by
  unfold readv_spec
  simp only [check_readv] at H
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
    try dsimp only at H ⊢
    generalize hr : readable_fd e = rr at H ⊢
    cases rr with
    | none =>
      try dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | some r =>
      try dsimp only at H ⊢
      by_cases hheap : readv_heap_iovecb iovcnt = true
      · rw [ite_eq_left hheap] at H ⊢
        unfold readv_heap_gap readv_buf_gap
        exact unmodeled_intro i m
      · rw [ite_eq_right hheap] at H ⊢
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at H ⊢
        cases imp with
        | ImpFault =>
          try dsimp only at H ⊢
          exact absurd H
            (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
        | ImpInval =>
          try dsimp only at H ⊢
          exact absurd H
            (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EINVAL) m [])
        | ImpOk iovs0 =>
          try dsimp only at H ⊢
          unfold check_copyin_prefix at H
          generalize hc : check_readv_imported i fd r iovs0
            (strip_copyin_prefix (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) eff) m
            = cres at H
          cases cres with
          | CheckUnmodeled =>
            try dsimp only at H
            exact record_copyins_unmodeled
              (readv_imported_sound_unmodeled i fd r iovs0 _ m hc)
          | CheckOk m'' evs'' =>
            try dsimp only at H
            by_cases hreads : access_ranges_eqb
              (eff.eff_copyins.take (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length)
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) = true
            · simp [hreads] at H
            · simp [hreads] at H
          | CheckReject =>
            try dsimp only at H
            by_cases hreads : access_ranges_eqb
              (eff.eff_copyins.take (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)).length)
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt)) = true
            · simp [hreads] at H
            · simp [hreads] at H

/-- `readv_spec` accepted implies `check_readv` accepts  The spec's ledger is the
    descriptor ranges CONCATENATED with the body's, so the checker's
    `strip_copyin_prefix` is the body's own ledger — `List.drop_left` —
    and `List.take_left` puts the prefix guard back. -/
theorem check_readv_complete_ok (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hs : readv_spec fd iov iovcnt i m (.ok eff m' evs)) :
    check_readv i fd iov iovcnt eff m = .CheckOk m' evs := by
  unfold readv_spec at Hs
  simp only [check_readv]
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    cases Hs
    simp [check_ret_only, bv_eqb_refl]
  | some e =>
    try dsimp only at Hs ⊢
    generalize hr : readable_fd e = rr at Hs ⊢
    cases rr with
    | none =>
      try dsimp only at Hs ⊢
      cases Hs
      simp [check_ret_only, bv_eqb_refl]
    | some r =>
      try dsimp only at Hs ⊢
      by_cases hheap : readv_heap_iovecb iovcnt = true
      · rw [ite_eq_left hheap] at Hs ⊢
        exact absurd Hs (readv_heap_gap_no_ok i m eff m' evs)
      · rw [ite_eq_right hheap] at Hs ⊢
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at Hs ⊢
        cases imp with
        | ImpFault =>
          try dsimp only at Hs ⊢
          obtain ⟨core, Hcore, heff⟩ := record_copyins_ok_inv _ _ i m eff m' evs Hs
          cases Hcore
          subst heff
          simp only [List.append_nil]
          exact check_ret_only_copyins_refl _ _ _ _
        | ImpInval =>
          try dsimp only at Hs ⊢
          obtain ⟨core, Hcore, heff⟩ := record_copyins_ok_inv _ _ i m eff m' evs Hs
          cases Hcore
          subst heff
          simp only [List.append_nil]
          exact check_ret_only_copyins_refl _ _ _ _
        | ImpOk iovs0 =>
          try dsimp only at Hs ⊢
          obtain ⟨core, Hcore, heff⟩ := record_copyins_ok_inv _ _ i m eff m' evs Hs
          have hb := readv_imported_complete_ok i fd r iovs0 core m m' evs Hcore
          subst heff
          have hstrip : strip_copyin_prefix
              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
              (with_copyins
                (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++ core.eff_copyins)
                core)
              = core := by
            simp only [strip_copyin_prefix, with_copyins, List.drop_left]
          rw [hstrip]
          rw [hb]
          unfold check_copyin_prefix
          try dsimp only
          simp [with_copyins, access_ranges_eqb_refl]

/-- `readv_spec` declining implies `check_readv` declines -/
theorem check_readv_complete_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (m : Model) (eff : SyscallEffect)
    (Hs : readv_spec fd iov iovcnt i m .unmodeled) :
    check_readv i fd iov iovcnt eff m = .CheckUnmodeled := by
  unfold readv_spec at Hs
  simp only [check_readv]
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    exact absurd Hs (pure_no_unmodeled _ i m)
  | some e =>
    try dsimp only at Hs ⊢
    generalize hr : readable_fd e = rr at Hs ⊢
    cases rr with
    | none =>
      try dsimp only at Hs ⊢
      exact absurd Hs (pure_no_unmodeled _ i m)
    | some r =>
      try dsimp only at Hs ⊢
      by_cases hheap : readv_heap_iovecb iovcnt = true
      · rw [ite_eq_left hheap] at Hs ⊢
        unfold check_readv_gap
        rfl
      · rw [ite_eq_right hheap] at Hs ⊢
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at Hs ⊢
        cases imp with
        | ImpFault =>
          try dsimp only at Hs ⊢
          exact absurd (record_copyins_unmodeled_inv _ _ i m Hs)
            (pure_no_unmodeled _ i m)
        | ImpInval =>
          try dsimp only at Hs ⊢
          exact absurd (record_copyins_unmodeled_inv _ _ i m Hs)
            (pure_no_unmodeled _ i m)
        | ImpOk iovs0 =>
          try dsimp only at Hs ⊢
          have h := record_copyins_unmodeled_inv _ _ i m Hs
          unfold check_copyin_prefix
          rw [readv_imported_complete_unmodeled i fd r iovs0 m _ h]
          try rfl

end LinuxSem.Checks.Sys.Fs.ReadWrite
