/-
  * LinuxProcessSem.Checks.Sys.Fs.ReadWrite.Vec — the writev (66) and
    readv (65) checkers' agreement proofs

  The `writev` (66) and `readv` (65) agreement proofs, split out of
  `Checks/Sys/Fs/ReadWrite.lean` because the four `writev` lemmas and the
  four `check_readv_imported` lemmas are the parts of that module's proof
  stack that walk the IOVEC IMPORT (`copy_iovecs_aux`, the `read_u64`
  chain, `gather_iovecs`/`import_iovecs`) and the per-buffer delivery loop,
  rather than the scalar syscalls the parent file's own proofs cover.

  The eight lemmas are `check_writev_{sound_ok,sound_unmodeled,complete_ok,
  complete_unmodeled}` and
  `check_readv_imported_{sound_ok,sound_unmodeled,complete_ok,
  complete_unmodeled}`, stated on the parent module's definitions.
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
   Leaves shared by the writev arms
   ========================================================================= -/

/-- An errno arm of a `record_copyins`-ledger spec, from the
    checker's `check_ret_only_copyins` acceptance.  The same step
    `check_pwrite64_sound_ok` takes arm by arm. -/
private theorem wv_errno_leaf (i : SyscallInput) (reads : List (word × Nat))
    (e : Int) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ret_only_copyins reads eff (errno_ret e) m [] = .CheckOk m' evs) :
    record_copyins reads (Sys.Syscall.err_ret e) i m (.ok eff m' evs) := by
  obtain ⟨heff, hm', hevs⟩ :=
    (check_ret_only_copyins_ok_iff reads eff (errno_ret e) m [] m' evs).mp H
  subst heff
  subst hm'
  subst hevs
  exact record_copyins_ok_empty (reads := reads) rfl (pure_ok _ i _)

/-- The zero-aggregate / zero-count leaf, which the spec spells
    `ret_only` and the checker `check_ret_only_copyins`. -/
private theorem wv_ret_only_copyins_leaf (i : SyscallInput)
    (reads : List (word × Nat)) (r : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_ret_only_copyins reads eff r m [] = .CheckOk m' evs) :
    record_copyins reads (Sys.Syscall.ret_only r) i m (.ok eff m' evs) := by
  obtain ⟨heff, hm', hevs⟩ :=
    (check_ret_only_copyins_ok_iff reads eff r m [] m' evs).mp H
  subst heff
  subst hm'
  subst hevs
  exact record_copyins_ok_empty (reads := reads) rfl (pure_ok _ i _)

/-- The deliver stage of a channel writev: emit one event per
    delivered byte and record the delivered prefix's ledger.  The mirror
    of `seqSpec_set_stdin_deliver_ok`, on the write side's shape. -/
private theorem seqSpec_emit_record_copyins_ok (ch : word)
    (reads : List (word × Nat)) (bs : List byte) (i : SyscallInput) (m : Model) :
    seqSpec (emit (bs.map (event.WriteEv ch)))
      (record_copyins reads (Sys.Syscall.ret_only (len_word bs))) i m
      (.ok (with_copyins reads (mkEffect (len_word bs) [] [])) m
        (bs.map (event.WriteEv ch))) := by
  refine ⟨(), m, bs.map (event.WriteEv ch), [], emit_ok _ i m, ?_, by simp⟩
  exact record_copyins_ok_empty (reads := reads) rfl (pure_ok _ i m)

/-- The file arms' leaf — the two state updates and the shared
    ledger, in the order `writev_spec`'s `place` writes them. -/
private theorem wv_file_leaf (fs' : Fs.Fs) (fds' : List (word × FdEntry))
    (reads1 reads2 : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model) :
    record_copyins reads1
      (seqSpec (set_fs fs')
        (seqSpec (set_fds fds')
          (record_copyins reads2 (Sys.Syscall.ret_only r)))) i m
      (.ok (with_copyins (reads1 ++ reads2) (mkEffect r [] []))
        (with_fds fds' (with_fs fs' m)) []) := by
  have h0 : record_copyins reads2 (Sys.Syscall.ret_only r) i
        (with_fds fds' (with_fs fs' m))
      (.ok (with_copyins reads2 (mkEffect r [] []))
        (with_fds fds' (with_fs fs' m)) []) :=
    record_copyins_ok_empty (reads := reads2) rfl (pure_ok _ i _)
  have h1 : seqSpec (set_fds fds') (record_copyins reads2 (Sys.Syscall.ret_only r))
      i (with_fs fs' m)
      (.ok (with_copyins reads2 (mkEffect r [] []))
        (with_fds fds' (with_fs fs' m)) []) :=
    ⟨(), with_fds fds' (with_fs fs' m), [], [], rfl, h0, by simp⟩
  have h2 : seqSpec (set_fs fs') (seqSpec (set_fds fds')
      (record_copyins reads2 (Sys.Syscall.ret_only r))) i m
      (.ok (with_copyins reads2 (mkEffect r [] []))
        (with_fds fds' (with_fs fs' m)) []) :=
    ⟨(), with_fs fs' m, [], [], rfl, h1, by simp⟩
  exact record_copyins_ok (reads := reads1) h2


/-- Invert one `record_copyins` layer. -/
private theorem wv_record_copyins_inv (reads : List (word × Nat))
    (S : SysSpec SyscallEffect) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : record_copyins reads S i m (.ok eff m' evs)) :
    ∃ eff0 m0 evs0, S i m (.ok eff0 m0 evs0) ∧
      eff = with_copyins (reads ++ eff0.eff_copyins) eff0 ∧ m' = m0 ∧ evs = evs0 := by
  unfold record_copyins LinuxSem.LinuxProcessSem.pure at H
  obtain ⟨x, m1, evs1, evs2, h1, h2, h3⟩ := H
  cases h2
  simp only [List.append_nil] at h3
  exact ⟨x, m', evs1, h1, rfl, rfl, h3⟩

/-- The accepted outcome of a bare `ret_only` leaf. -/
private theorem wv_ret_only_outcome (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : Sys.Syscall.ret_only r i m (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = m ∧ evs = [] := by
  unfold Sys.Syscall.ret_only LinuxSem.LinuxProcessSem.pure at H
  cases H
  exact ⟨rfl, rfl, rfl⟩

/-- Invert `record_copyins` over an `err_ret` leaf. -/
private theorem wv_err_ret_inv (i : SyscallInput) (reads : List (word × Nat))
    (e : Int) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : record_copyins reads (Sys.Syscall.err_ret e) i m (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect (errno_ret e) [] []) ∧ m' = m ∧ evs = [] := by
  obtain ⟨eff0, m0, evs0, h1, h2, h3, h4⟩ := wv_record_copyins_inv reads _ i m eff m' evs H
  unfold Sys.Syscall.err_ret Sys.Syscall.ret_only
    LinuxSem.LinuxProcessSem.pure at h1
  cases h1
  refine ⟨?_, h3, h4⟩
  rw [h2]
  simp [with_copyins]

/-- Invert `record_copyins` over a `ret_only` leaf. -/
private theorem wv_ret_only_inv (i : SyscallInput) (reads : List (word × Nat))
    (r : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : record_copyins reads (Sys.Syscall.ret_only r) i m (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] []) ∧ m' = m ∧ evs = [] := by
  obtain ⟨eff0, m0, evs0, h1, h2, h3, h4⟩ := wv_record_copyins_inv reads _ i m eff m' evs H
  obtain ⟨h5, h6, h7⟩ := wv_ret_only_outcome r i m eff0 m0 evs0 h1
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, h5]
    simp [with_copyins]
  · rw [h3, h6]
  · rw [h4, h7]

/-- Invert an accepted `seqSpec (set_fs fs') k` — `set_fs` is a
    `modifySpec`, so it cannot fail and the continuation runs at the
    updated model. -/
private theorem seqSpec_set_fs_ok_inv (fs' : Fs.Fs) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : seqSpec (set_fs fs') k i m (.ok eff m' evs)) :
    k i (with_fs fs' m) (.ok eff m' evs) := by
  unfold seqSpec set_fs modifySpec LinuxSem.LinuxProcessSem.modify
    LinuxSem.LinuxProcessSem.bind at H
  obtain ⟨u, m1, evs1, evs2, h1, h2, h3⟩ := H
  simp only [Outcome.ok.injEq] at h1
  obtain ⟨-, hm, hevs1⟩ := h1
  subst hm
  subst hevs1
  rw [h3]
  exact h2

/-- The same for `set_fds`. -/
private theorem seqSpec_set_fds_ok_inv (fds : List (word × FdEntry))
    (k : SysSpec SyscallEffect) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds) k i m (.ok eff m' evs)) :
    k i (with_fds fds m) (.ok eff m' evs) := by
  unfold seqSpec set_fds modifySpec LinuxSem.LinuxProcessSem.modify
    LinuxSem.LinuxProcessSem.bind at H
  obtain ⟨u, m1, evs1, evs2, h1, h2, h3⟩ := H
  simp only [Outcome.ok.injEq] at h1
  obtain ⟨-, hm, hevs1⟩ := h1
  subst hm
  subst hevs1
  rw [h3]
  exact h2

/-- Invert the file arms' leaf (the two state updates and the
    ledger) in the completeness direction. -/
private theorem wv_file_leaf_inv (fs' : Fs.Fs) (fds' : List (word × FdEntry))
    (reads1 reads2 : List (word × Nat)) (r : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : record_copyins reads1
      (seqSpec (set_fs fs')
        (seqSpec (set_fds fds')
          (record_copyins reads2 (Sys.Syscall.ret_only r)))) i m (.ok eff m' evs)) :
    eff = with_copyins (reads1 ++ reads2) (mkEffect r [] []) ∧
      m' = with_fds fds' (with_fs fs' m) ∧ evs = [] := by
  obtain ⟨eff1, m1, evs1, h1, heff, hm, hevs⟩ :=
    wv_record_copyins_inv reads1 _ i m eff m' evs H
  have h2 := seqSpec_set_fs_ok_inv fs' _ i m eff1 m1 evs1 h1
  have h3 := seqSpec_set_fds_ok_inv fds' _ i (with_fs fs' m) eff1 m1 evs1 h2
  obtain ⟨eff0, m0, evs0, h4, h5, h6, h7⟩ :=
    wv_record_copyins_inv reads2 _ i (with_fds fds' (with_fs fs' m)) eff1 m1 evs1 h3
  obtain ⟨h8, h9, h10⟩ :=
    wv_ret_only_outcome r i (with_fds fds' (with_fs fs' m)) eff0 m0 evs0 h4
  refine ⟨?_, ?_, ?_⟩
  · rw [heff, h5, h8]
    simp [with_copyins, List.append_nil]
  · rw [hm, h6, h9]
  · rw [hevs, h7, h10]


/-- A `writev_buf_gap` leaf admits no accepted outcome. -/
private theorem wv_buf_gap_no_ok (reads : List (word × Nat)) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : record_copyins reads writev_buf_gap i m (.ok eff m' evs)) : False := by
  obtain ⟨eff0, m0, evs0, h1, -, -, -⟩ := wv_record_copyins_inv reads _ i m eff m' evs H
  unfold writev_buf_gap LinuxSem.LinuxProcessSem.unmodeled at h1
  exact nomatch h1

/-- Invert the channel writev's accepted delivery leaf. -/
private theorem wv_channel_leaf_inv (ch : word) (iovs0 : List (word × word))
    (i : SyscallInput) (reads1 : List (word × Nat)) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event) (bs : List byte)
    (H : record_copyins reads1
      (bind (choose (fun ds : List byte =>
          1 ≤ (ds.length : Int) ∧ (ds.length : Int) < two_pow_64 ∧
          addr_is_error_b (len_word ds) = false ∧ ds = bs.take ds.length))
        (fun ds => seqSpec (emit (ds.map (event.WriteEv ch)))
          (record_copyins (iov_prefix_accesses (cap_iovecs iovs0) ds.length)
            (Sys.Syscall.ret_only (len_word ds))))) i m (.ok eff m' evs)) :
    ∃ ds : List byte,
      (1 ≤ (ds.length : Int) ∧ (ds.length : Int) < two_pow_64 ∧
       addr_is_error_b (len_word ds) = false ∧ ds = bs.take ds.length) ∧
      eff = with_copyins (reads1 ++ iov_prefix_accesses (cap_iovecs iovs0) ds.length)
              (mkEffect (len_word ds) [] []) ∧
      m' = m ∧ evs = ds.map (event.WriteEv ch) := by
  obtain ⟨eff0, m0, evs0, h1, heff, hm, hevs⟩ :=
    wv_record_copyins_inv reads1 _ i m eff m' evs H
  unfold LinuxSem.LinuxProcessSem.bind at h1
  obtain ⟨ds, m1, evs1, evs2, hc, hk, h3⟩ := h1
  unfold LinuxSem.LinuxProcessSem.choose at hc
  obtain ⟨ds', hP, hEq⟩ := hc
  cases hEq
  unfold seqSpec LinuxSem.LinuxProcessSem.bind at hk
  obtain ⟨u, m2, evs3, evs4, h4, h5, h6⟩ := hk
  unfold LinuxSem.LinuxProcessSem.emit at h4
  cases h4
  obtain ⟨h7, h8, h9⟩ :=
    wv_ret_only_inv i (iov_prefix_accesses (cap_iovecs iovs0) ds.length)
      (len_word ds) eff0 m m0 evs4 h5
  refine ⟨ds, hP, ?_, ?_, ?_⟩
  · rw [heff, h7]
    simp [with_copyins]
  · rw [hm, h8]
  · rw [hevs, h3, h6, h9]
    simp

theorem check_writev_sound_ok (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_writev i fd iov iovcnt eff m = .CheckOk m' evs) :
    writev_spec fd iov iovcnt i m (.ok eff m' evs) := by
  unfold writev_spec
  simp only [check_writev] at H
  refine bind_ok0 (c := inputSpec) ?_ i m i m eff m' evs (input_ok i m) ?_
  try dsimp only
  refine bind_ok0 (c := getModelSpec) ?_ i m m m eff m' evs rfl ?_
  try dsimp only
  unfold writev_file_arm writev_ledger
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
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at H ⊢
          exact wv_errno_leaf i _ EFAULT eff m m' evs H
        | ImpInval =>
          simp only [hiv] at H ⊢
          exact wv_errno_leaf i _ EINVAL eff m m' evs H
        | ImpOk iovs0 =>
          simp only [hiv] at H ⊢
          try dsimp only at H ⊢
          generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
          try dsimp only at H ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at H ⊢
            exact wv_ret_only_copyins_leaf i _ (BitVec.ofInt 64 0) eff m m' evs H
          · rw [ite_eq_right htot] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H ⊢
              exact wv_errno_leaf i _ EFAULT eff m m' evs H
            · rw [ite_eq_right hbl] at H ⊢
              by_cases hae : addr_is_error_b (len_word bs) = true
              · rw [ite_eq_left hae] at H
                exact nomatch H
              · rw [ite_eq_right hae] at H ⊢
                obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
                cases ws with
                | nil =>
                  cases zs with
                  | nil =>
                    cases us with
                    | nil =>
                      cases cs with
                      | nil =>
                        try dsimp only at H ⊢
                        by_cases hg : (decide (1 ≤ (ret.toNat : Int))
                            && decide ((ret.toNat : Int) ≤ (bs.length : Int))
                            && !(addr_is_error_b ret)) = true
                        · rw [ite_eq_left hg] at H
                          by_cases hr : access_ranges_eqb copyins
                              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                               iov_prefix_accesses (cap_iovecs iovs0) ret.toNat) = true
                          · rw [ite_eq_left hr] at H
                            cases H
                            have hg' : decide (1 ≤ (ret.toNat : Int)) = true ∧
                                decide ((ret.toNat : Int) ≤ (bs.length : Int)) = true ∧
                                (!(addr_is_error_b ret)) = true := by
                              simpa [Bool.and_eq_true, and_assoc] using hg
                            obtain ⟨h1, h2, h3⟩ := hg'
                            have h1' : 1 ≤ (ret.toNat : Int) := of_decide_eq_true h1
                            have h2' : (ret.toNat : Int) ≤ (bs.length : Int) :=
                              of_decide_eq_true h2
                            have h3' : addr_is_error_b ret = false := by
                              simpa using h3
                            have h0 : 0 ≤ (ret.toNat : Int) := by omega
                            have hlen : (bs.take ret.toNat).length = ret.toNat := by
                              rw [List.length_take]
                              exact Nat.min_eq_left (Int.toNat_le.mpr h2')
                            have hlw : len_word (bs.take ret.toNat) = ret :=
                              len_word_firstn_ret ret bs ⟨h0, h2'⟩
                            have hcopy : copyins = import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                                iov_prefix_accesses (cap_iovecs iovs0) ret.toNat :=
                              (access_ranges_eqb_eq _ _).mp hr
                            have heffeq : (⟨ret, [], [], [], [], copyins⟩ : SyscallEffect)
                                = with_copyins
                                    (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                                     iov_prefix_accesses (cap_iovecs iovs0) (bs.take ret.toNat).length)
                                    ⟨len_word (bs.take ret.toNat), [], [], [], [],
                                     iov_prefix_accesses (cap_iovecs iovs0) (bs.take ret.toNat).length⟩ := by
                              simp only [hlen, hlw, hcopy]
                              rfl
                            rw [heffeq]
                            refine ⟨⟨len_word (bs.take ret.toNat), [], [], [], [],
                                      iov_prefix_accesses (cap_iovecs iovs0) (bs.take ret.toNat).length⟩,
                                    m, (bs.take ret.toNat).map (event.WriteEv ch), [], ?_,
                                    pure_ok _ i _, by simp⟩
                            refine ⟨bs.take ret.toNat, m, [], (bs.take ret.toNat).map (event.WriteEv ch),
                              ?_, ?_, rfl⟩
                            · refine choose_ok _ _ i m ⟨?_, ?_, ?_, ?_⟩
                              · rw [hlen]; exact h1'
                              · rw [hlen]
                                have hlt := ret.isLt
                                unfold two_pow_64
                                omega
                              · rw [hlw]; exact h3'
                              · exact congrArg (fun n => bs.take n) hlen.symm
                            · exact seqSpec_emit_record_copyins_ok ch _ _ i m
                          · rw [ite_eq_right hr] at H
                            exact nomatch H
                        · rw [ite_eq_right hg] at H
                          exact nomatch H
                      | cons _ _ => try dsimp only at H; exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
    | FdFile p off =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | FdFileW p off =>
      try dsimp only at H ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at H ⊢
        exact wv_errno_leaf i _ EFAULT eff m m' evs H
      | ImpInval =>
        simp only [hiv] at H ⊢
        exact wv_errno_leaf i _ EINVAL eff m m' evs H
      | ImpOk iovs0 =>
        simp only [hiv] at H ⊢
        try dsimp only at H ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
        try dsimp only at H ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at H ⊢
          exact wv_ret_only_copyins_leaf i _ (BitVec.ofInt 64 0) eff m m' evs H
        · rw [ite_eq_right htot] at H ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at H ⊢
            exact wv_errno_leaf i _ EINVAL eff m m' evs H
          · rw [ite_eq_right hpos] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H ⊢
              exact wv_errno_leaf i _ EFAULT eff m m' evs H
            · rw [ite_eq_right hbl] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hmg] at H ⊢
                  dsimp only at ⊢
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at H ⊢
                    exact nomatch H
                  · rw [ite_eq_right hae] at H ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      (check_ret_only_copyins_ok_iff
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                         iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                        eff (len_word bs)
                        (with_fds (fd_insert (m_fds m) fd
                           (FdEntry.FdFileW p (off + len_word bs)))
                          (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                        [] m' evs).mp H
                    subst heff
                    rw [hm']
                    subst hevs
                    exact wv_file_leaf (Fs.fs_set (m_fs m) p (Fs.file_write data off bs))
                      (fd_insert (m_fds m) fd (FdEntry.FdFileW p (off + len_word bs)))
                      (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                      (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                      (len_word bs) i m
    | FdFileA p off =>
      try dsimp only at H ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at H ⊢
        exact wv_errno_leaf i _ EFAULT eff m m' evs H
      | ImpInval =>
        simp only [hiv] at H ⊢
        exact wv_errno_leaf i _ EINVAL eff m m' evs H
      | ImpOk iovs0 =>
        simp only [hiv] at H ⊢
        try dsimp only at H ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
        try dsimp only at H ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at H ⊢
          exact wv_ret_only_copyins_leaf i _ (BitVec.ofInt 64 0) eff m m' evs H
        · rw [ite_eq_right htot] at H ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at H ⊢
            exact wv_errno_leaf i _ EINVAL eff m m' evs H
          · rw [ite_eq_right hpos] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H ⊢
              exact wv_errno_leaf i _ EFAULT eff m m' evs H
            · rw [ite_eq_right hbl] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                by_cases hae : addr_is_error_b (len_word bs) = true
                · rw [ite_eq_left hae] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hae] at H ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    (check_ret_only_copyins_ok_iff
                      (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                       iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                      eff (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                         (FdEntry.FdFileA p (append_new_pos data bs off)))
                        (with_fs (Fs.fs_set (m_fs m) p
                           (Fs.file_write data (len_word data) bs)) m))
                      [] m' evs).mp H
                  subst heff
                  rw [hm']
                  subst hevs
                  exact wv_file_leaf (Fs.fs_set (m_fs m) p
                      (Fs.file_write data (len_word data) bs))
                    (fd_insert (m_fds m) fd (FdEntry.FdFileA p (append_new_pos data bs off)))
                    (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                    (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                    (len_word bs) i m
    | FdFileRW p off =>
      try dsimp only at H ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at H ⊢
        exact wv_errno_leaf i _ EFAULT eff m m' evs H
      | ImpInval =>
        simp only [hiv] at H ⊢
        exact wv_errno_leaf i _ EINVAL eff m m' evs H
      | ImpOk iovs0 =>
        simp only [hiv] at H ⊢
        try dsimp only at H ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
        try dsimp only at H ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at H ⊢
          exact wv_ret_only_copyins_leaf i _ (BitVec.ofInt 64 0) eff m m' evs H
        · rw [ite_eq_right htot] at H ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at H ⊢
            exact wv_errno_leaf i _ EINVAL eff m m' evs H
          · rw [ite_eq_right hpos] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H ⊢
              exact wv_errno_leaf i _ EFAULT eff m m' evs H
            · rw [ite_eq_right hbl] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H
                exact nomatch H
              | some data =>
                simp only [hfs] at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hmg] at H ⊢
                  dsimp only at ⊢
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at H ⊢
                    exact nomatch H
                  · rw [ite_eq_right hae] at H ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      (check_ret_only_copyins_ok_iff
                        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                         iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                        eff (len_word bs)
                        (with_fds (fd_insert (m_fds m) fd
                           (FdEntry.FdFileRW p (off + len_word bs)))
                          (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                        [] m' evs).mp H
                    subst heff
                    rw [hm']
                    subst hevs
                    exact wv_file_leaf (Fs.fs_set (m_fs m) p (Fs.file_write data off bs))
                      (fd_insert (m_fds m) fd (FdEntry.FdFileRW p (off + len_word bs)))
                      (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
                      (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                      (len_word bs) i m
    | FdDir =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | FdSocket sk =>
      try dsimp only at H ⊢
      exact nomatch H
    | FdPipe id w =>
      try dsimp only at H ⊢
      by_cases hw : (!w) = true
      · rw [ite_eq_left hw] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hw] at H ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at H ⊢
          exact wv_errno_leaf i _ EFAULT eff m m' evs H
        | ImpInval =>
          simp only [hiv] at H ⊢
          exact wv_errno_leaf i _ EINVAL eff m m' evs H
        | ImpOk iovs0 =>
          simp only [hiv] at H ⊢
          try dsimp only at H ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at H ⊢
            exact wv_ret_only_copyins_leaf i _ (BitVec.ofInt 64 0) eff m m' evs H
          · rw [ite_eq_right htot] at H
            exact nomatch H
    | FdDevNull rd wr =>
      try dsimp only at H ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at H ⊢
        exact ret_only_ok_spec H i
      · rw [ite_eq_right hwr] at H ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at H ⊢
          exact wv_errno_leaf i _ EFAULT eff m m' evs H
        | ImpInval =>
          simp only [hiv] at H ⊢
          exact wv_errno_leaf i _ EINVAL eff m m' evs H
        | ImpOk iovs0 =>
          simp only [hiv] at H ⊢
          try dsimp only at H ⊢
          exact wv_ret_only_copyins_leaf i _
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) eff m m' evs H
    | FdUrandom =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i

theorem check_writev_sound_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_writev i fd iov iovcnt eff m = .CheckUnmodeled) :
    writev_spec fd iov iovcnt i m .unmodeled := by
  unfold writev_spec
  simp only [check_writev] at H
  refine bind_unmodeled2 (c := inputSpec) ?_ i m i m [] (input_ok i m) ?_
  try dsimp only
  refine bind_unmodeled2 (c := getModelSpec) ?_ i m m m [] rfl ?_
  try dsimp only
  unfold writev_file_arm writev_ledger
  generalize hq : fd_lookup (m_fds m) fd = q at H ⊢
  cases q with
  | none =>
    try dsimp only at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at H ⊢
      by_cases hw : w_is0 ch = true
      · rw [ite_eq_left hw] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hw] at H ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (errno_ret EFAULT) m [])
        | ImpInval =>
          simp only [hiv] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (errno_ret EINVAL) m [])
        | ImpOk iovs0 =>
          simp only [hiv] at H ⊢
          try dsimp only at H ⊢
          generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
          try dsimp only at H ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at H
            exact absurd H (check_ret_only_copyins_no_unmodeled _
              eff (BitVec.ofInt 64 0) m [])
          · rw [ite_eq_right htot] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H
              exact absurd H (check_ret_only_copyins_no_unmodeled _
                eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hbl] at H ⊢
              by_cases hae : addr_is_error_b (len_word bs) = true
              · rw [ite_eq_left hae] at H ⊢
                exact record_copyins_unmodeled (unmodeled_intro i m)
              · rw [ite_eq_right hae] at H ⊢
                obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
                cases ws with
                | nil =>
                  cases zs with
                  | nil =>
                    cases us with
                    | nil =>
                      cases cs with
                      | nil =>
                        try dsimp only at H
                        by_cases hg : (decide (1 ≤ (ret.toNat : Int))
                            && decide ((ret.toNat : Int) ≤ (bs.length : Int))
                            && !(addr_is_error_b ret)) = true
                        · rw [ite_eq_left hg] at H
                          by_cases hr : access_ranges_eqb copyins
                              (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt) ++
                               iov_prefix_accesses (cap_iovecs iovs0) ret.toNat) = true
                          · rw [ite_eq_left hr] at H
                            exact nomatch H
                          · rw [ite_eq_right hr] at H
                            exact nomatch H
                        · rw [ite_eq_right hg] at H
                          exact nomatch H
                      | cons _ _ => try dsimp only at H; exact nomatch H
                    | cons _ _ => try dsimp only at H; exact nomatch H
                  | cons _ _ => try dsimp only at H; exact nomatch H
                | cons _ _ => try dsimp only at H; exact nomatch H
    | FdFile p off =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | FdFileW p off =>
      try dsimp only at H ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _
          eff (errno_ret EFAULT) m [])
      | ImpInval =>
        simp only [hiv] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _
          eff (errno_ret EINVAL) m [])
      | ImpOk iovs0 =>
        simp only [hiv] at H ⊢
        try dsimp only at H ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
        try dsimp only at H ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (BitVec.ofInt 64 0) m [])
        · rw [ite_eq_right htot] at H ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at H
            exact absurd H (check_ret_only_copyins_no_unmodeled _
              eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hpos] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H
              exact absurd H (check_ret_only_copyins_no_unmodeled _
                eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hbl] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H ⊢
                exact record_copyins_unmodeled (unmodeled_intro i m)
              | some data =>
                simp only [hfs] at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact record_copyins_unmodeled (unmodeled_intro i m)
                · rw [ite_eq_right hmg] at H ⊢
                  dsimp only at ⊢
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at H ⊢
                    exact record_copyins_unmodeled (unmodeled_intro i m)
                  · rw [ite_eq_right hae] at H
                    exact absurd H (check_ret_only_copyins_no_unmodeled _
                      eff (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                         (FdEntry.FdFileW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)) [])
    | FdFileA p off =>
      try dsimp only at H ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _
          eff (errno_ret EFAULT) m [])
      | ImpInval =>
        simp only [hiv] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _
          eff (errno_ret EINVAL) m [])
      | ImpOk iovs0 =>
        simp only [hiv] at H ⊢
        try dsimp only at H ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
        try dsimp only at H ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (BitVec.ofInt 64 0) m [])
        · rw [ite_eq_right htot] at H ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at H
            exact absurd H (check_ret_only_copyins_no_unmodeled _
              eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hpos] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H
              exact absurd H (check_ret_only_copyins_no_unmodeled _
                eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hbl] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H ⊢
                exact record_copyins_unmodeled (unmodeled_intro i m)
              | some data =>
                simp only [hfs] at H ⊢
                by_cases hae : addr_is_error_b (len_word bs) = true
                · rw [ite_eq_left hae] at H ⊢
                  exact record_copyins_unmodeled (unmodeled_intro i m)
                · rw [ite_eq_right hae] at H
                  exact absurd H (check_ret_only_copyins_no_unmodeled _
                    eff (len_word bs)
                    (with_fds (fd_insert (m_fds m) fd
                       (FdEntry.FdFileA p (append_new_pos data bs off)))
                      (with_fs (Fs.fs_set (m_fs m) p
                         (Fs.file_write data (len_word data) bs)) m)) [])
    | FdFileRW p off =>
      try dsimp only at H ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _
          eff (errno_ret EFAULT) m [])
      | ImpInval =>
        simp only [hiv] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _
          eff (errno_ret EINVAL) m [])
      | ImpOk iovs0 =>
        simp only [hiv] at H ⊢
        try dsimp only at H ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at H ⊢
        try dsimp only at H ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (BitVec.ofInt 64 0) m [])
        · rw [ite_eq_right htot] at H ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at H
            exact absurd H (check_ret_only_copyins_no_unmodeled _
              eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hpos] at H ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at H
              exact absurd H (check_ret_only_copyins_no_unmodeled _
                eff (errno_ret EFAULT) m [])
            · rw [ite_eq_right hbl] at H ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at H ⊢
                exact record_copyins_unmodeled (unmodeled_intro i m)
              | some data =>
                simp only [hfs] at H ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at H ⊢
                  exact record_copyins_unmodeled (unmodeled_intro i m)
                · rw [ite_eq_right hmg] at H ⊢
                  dsimp only at ⊢
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at H ⊢
                    exact record_copyins_unmodeled (unmodeled_intro i m)
                  · rw [ite_eq_right hae] at H
                    exact absurd H (check_ret_only_copyins_no_unmodeled _
                      eff (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                         (FdEntry.FdFileRW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)) [])
    | FdDir =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | FdSocket sk =>
      try dsimp only at H ⊢
      unfold writev_buf_gap
      exact unmodeled_intro i m
    | FdPipe id w =>
      try dsimp only at H ⊢
      by_cases hw : (!w) = true
      · rw [ite_eq_left hw] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hw] at H ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (errno_ret EFAULT) m [])
        | ImpInval =>
          simp only [hiv] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (errno_ret EINVAL) m [])
        | ImpOk iovs0 =>
          simp only [hiv] at H ⊢
          try dsimp only at H ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at H
            exact absurd H (check_ret_only_copyins_no_unmodeled _
              eff (BitVec.ofInt 64 0) m [])
          · rw [ite_eq_right htot] at H ⊢
            exact record_copyins_unmodeled (unmodeled_intro i m)
    | FdDevNull rd wr =>
      try dsimp only at H ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hwr] at H ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (errno_ret EFAULT) m [])
        | ImpInval =>
          simp only [hiv] at H
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (errno_ret EINVAL) m [])
        | ImpOk iovs0 =>
          simp only [hiv] at H ⊢
          try dsimp only at H ⊢
          exact absurd H (check_ret_only_copyins_no_unmodeled _
            eff (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) m [])
    | FdUrandom =>
      try dsimp only at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])

theorem check_writev_complete_ok (i : SyscallInput) (fd iov iovcnt : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hs : writev_spec fd iov iovcnt i m (.ok eff m' evs)) :
    check_writev i fd iov iovcnt eff m = .CheckOk m' evs := by
  unfold writev_spec at Hs
  simp only [check_writev]
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  unfold writev_file_arm writev_ledger at Hs
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
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_err_ret_inv i _ EFAULT eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
        | ImpInval =>
          simp only [hiv] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_err_ret_inv i _ EINVAL eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
        | ImpOk iovs0 =>
          simp only [hiv] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at Hs ⊢
            obtain ⟨heff, hm', hevs⟩ :=
              wv_ret_only_inv i _ (BitVec.ofInt 64 0) eff m m' evs Hs
            subst heff
            rw [hm']
            subst hevs
            exact check_ret_only_copyins_refl _ (BitVec.ofInt 64 0) m []
          · rw [ite_eq_right htot] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                wv_err_ret_inv i _ EFAULT eff m m' evs Hs
              subst heff
              rw [hm']
              subst hevs
              exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
            · rw [ite_eq_right hbl] at Hs ⊢
              by_cases hae : addr_is_error_b (len_word bs) = true
              · rw [ite_eq_left hae] at Hs ⊢
                exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
              · rw [ite_eq_right hae] at Hs ⊢
                obtain ⟨ds, hP, heff, hm', hevs⟩ :=
                  wv_channel_leaf_inv ch iovs0 i _ m eff m' evs bs Hs
                obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
                rw [heff, hm', hevs]
                simp only [with_copyins]
                have hlen : (len_word ds).toNat = ds.length := by
                  have h := len_word_unsigned ds hP2
                  omega
                rw [show bs.take (len_word ds).toNat = ds by rw [hlen, ← hP4]]
                rw [hlen]
                have hle : (ds.length : Int) ≤ (bs.length : Int) := by
                  have h2 : ds.length ≤ bs.length := by
                    rw [hP4, List.length_take]
                    omega
                  omega
                have hg : (decide (1 ≤ (ds.length : Int))
                    && decide ((ds.length : Int) ≤ (bs.length : Int))
                    && !(addr_is_error_b (len_word ds))) = true := by
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨⟨hP1, hle⟩, by simpa using hP3⟩
                rw [ite_eq_left hg]
                rw [ite_eq_left (access_ranges_eqb_refl _)]
                try rfl
    | FdFile p off =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | FdFileW p off =>
      try dsimp only at Hs ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
        subst heff
        rw [hm']
        subst hevs
        exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
      | ImpInval =>
        simp only [hiv] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
        subst heff
        rw [hm']
        subst hevs
        exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
      | ImpOk iovs0 =>
        simp only [hiv] at Hs ⊢
        try dsimp only at Hs ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_inv i _ (BitVec.ofInt 64 0) eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (BitVec.ofInt 64 0) m []
        · rw [ite_eq_right htot] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
            subst heff
            rw [hm']
            subst hevs
            exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
          · rw [ite_eq_right hpos] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
              subst heff
              rw [hm']
              subst hevs
              exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
            · rw [ite_eq_right hbl] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
              | some data =>
                simp only [hfs] at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at Hs ⊢
                    exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
                  · rw [ite_eq_right hae] at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      wv_file_leaf_inv (Fs.fs_set (m_fs m) p (Fs.file_write data off bs))
                        (fd_insert (m_fds m) fd (FdEntry.FdFileW p (off + len_word bs)))
                        _ _ (len_word bs) i m eff m' evs Hs
                    subst heff
                    rw [hm']
                    subst hevs
                    exact check_ret_only_copyins_refl _ (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                         (FdEntry.FdFileW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)) []
    | FdFileA p off =>
      try dsimp only at Hs ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
        subst heff
        rw [hm']
        subst hevs
        exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
      | ImpInval =>
        simp only [hiv] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
        subst heff
        rw [hm']
        subst hevs
        exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
      | ImpOk iovs0 =>
        simp only [hiv] at Hs ⊢
        try dsimp only at Hs ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_inv i _ (BitVec.ofInt 64 0) eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (BitVec.ofInt 64 0) m []
        · rw [ite_eq_right htot] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
            subst heff
            rw [hm']
            subst hevs
            exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
          · rw [ite_eq_right hpos] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
              subst heff
              rw [hm']
              subst hevs
              exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
            · rw [ite_eq_right hbl] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs
                by_cases hae : addr_is_error_b (len_word bs) = true
                · rw [ite_eq_left hae] at Hs ⊢
                  exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
                · rw [ite_eq_right hae] at Hs ⊢
                  obtain ⟨heff, hm', hevs⟩ :=
                    wv_file_leaf_inv (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs))
                      (fd_insert (m_fds m) fd (FdEntry.FdFileA p (append_new_pos data bs off)))
                      _ _ (len_word bs) i m eff m' evs Hs
                  subst heff
                  rw [hm']
                  subst hevs
                  exact check_ret_only_copyins_refl _ (len_word bs)
                    (with_fds (fd_insert (m_fds m) fd
                       (FdEntry.FdFileA p (append_new_pos data bs off)))
                      (with_fs (Fs.fs_set (m_fs m) p
                         (Fs.file_write data (len_word data) bs)) m)) []
    | FdFileRW p off =>
      try dsimp only at Hs ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
        subst heff
        rw [hm']
        subst hevs
        exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
      | ImpInval =>
        simp only [hiv] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
        subst heff
        rw [hm']
        subst hevs
        exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
      | ImpOk iovs0 =>
        simp only [hiv] at Hs ⊢
        try dsimp only at Hs ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_inv i _ (BitVec.ofInt 64 0) eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (BitVec.ofInt 64 0) m []
        · rw [ite_eq_right htot] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
            subst heff
            rw [hm']
            subst hevs
            exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
          · rw [ite_eq_right hpos] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
              subst heff
              rw [hm']
              subst hevs
              exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
            · rw [ite_eq_right hbl] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs
                exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
              | some data =>
                simp only [hfs] at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at Hs ⊢
                    exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
                  · rw [ite_eq_right hae] at Hs ⊢
                    obtain ⟨heff, hm', hevs⟩ :=
                      wv_file_leaf_inv (Fs.fs_set (m_fs m) p (Fs.file_write data off bs))
                        (fd_insert (m_fds m) fd (FdEntry.FdFileRW p (off + len_word bs)))
                        _ _ (len_word bs) i m eff m' evs Hs
                    subst heff
                    rw [hm']
                    subst hevs
                    exact check_ret_only_copyins_refl _ (len_word bs)
                      (with_fds (fd_insert (m_fds m) fd
                         (FdEntry.FdFileRW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)) []
    | FdDir =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]
    | FdSocket sk =>
      try dsimp only at Hs ⊢
      unfold writev_buf_gap LinuxSem.LinuxProcessSem.unmodeled at Hs
      exact nomatch Hs
    | FdPipe id w =>
      try dsimp only at Hs ⊢
      by_cases hw : (!w) = true
      · rw [ite_eq_left hw] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hw] at Hs ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
        | ImpInval =>
          simp only [hiv] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
        | ImpOk iovs0 =>
          simp only [hiv] at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at Hs ⊢
            obtain ⟨heff, hm', hevs⟩ :=
              wv_ret_only_inv i _ (BitVec.ofInt 64 0) eff m m' evs Hs
            subst heff
            rw [hm']
            subst hevs
            exact check_ret_only_copyins_refl _ (BitVec.ofInt 64 0) m []
          · rw [ite_eq_right htot] at Hs ⊢
            exact False.elim (wv_buf_gap_no_ok _ i m eff m' evs Hs)
    | FdDevNull rd wr =>
      try dsimp only at Hs ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at Hs ⊢
        cases Hs
        try simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hwr] at Hs ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EFAULT eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
        | ImpInval =>
          simp only [hiv] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ := wv_err_ret_inv i _ EINVAL eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _ (errno_ret EINVAL) m []
        | ImpOk iovs0 =>
          simp only [hiv] at Hs ⊢
          try dsimp only at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_inv i _ (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))
              eff m m' evs Hs
          subst heff
          rw [hm']
          subst hevs
          exact check_ret_only_copyins_refl _
            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) m []
    | FdUrandom =>
      try dsimp only at Hs ⊢
      cases Hs
      try simp [check_ret_only, bv_eqb_refl]

/-- `record_copyins` declines exactly when its inner spec does. -/
private theorem wv_record_copyins_no_unmodeled (reads : List (word × Nat))
    (S : SysSpec SyscallEffect) (i : SyscallInput) (m : Model)
    (hc : ¬ S i m .unmodeled) :
    ¬ record_copyins reads S i m .unmodeled := by
  unfold record_copyins
  exact bind_no_unmodeled S _ i m hc (fun a m1 evs1 _ => pure_no_unmodeled _ i m1)

/-- An `err_ret` leaf never declines. -/
private theorem wv_err_ret_no_unmodeled (e : Int) (i : SyscallInput) (m : Model) :
    ¬ (Sys.Syscall.err_ret e : SysSpec SyscallEffect) i m .unmodeled :=
  pure_no_unmodeled _ i m

/-- The file arms' leaf never declines. -/
private theorem wv_file_leaf_no_unmodeled (fs' : Fs.Fs)
    (fds' : List (word × FdEntry)) (reads1 reads2 : List (word × Nat))
    (r : word) (i : SyscallInput) (m : Model) :
    ¬ record_copyins reads1
      (seqSpec (set_fs fs')
        (seqSpec (set_fds fds')
          (record_copyins reads2 (Sys.Syscall.ret_only r)))) i m .unmodeled := by
  refine wv_record_copyins_no_unmodeled reads1 _ i m ?_
  refine modifySeq_no_unmodeled (with_fs fs') _ i m ?_
  refine modifySeq_no_unmodeled (with_fds fds') _ i (with_fs fs' m) ?_
  exact wv_record_copyins_no_unmodeled reads2 _ i _ (pure_no_unmodeled _ i _)

/-- The channel's delivery leaf never declines. -/
private theorem wv_channel_leaf_no_unmodeled (ch : word)
    (iovs0 : List (word × word)) (i : SyscallInput)
    (reads1 : List (word × Nat)) (m : Model) (bs : List byte) :
    ¬ record_copyins reads1
      (bind (choose (fun ds : List byte =>
          1 ≤ (ds.length : Int) ∧ (ds.length : Int) < two_pow_64 ∧
          addr_is_error_b (len_word ds) = false ∧ ds = bs.take ds.length))
        (fun ds => seqSpec (emit (ds.map (event.WriteEv ch)))
          (record_copyins (iov_prefix_accesses (cap_iovecs iovs0) ds.length)
            (Sys.Syscall.ret_only (len_word ds))))) i m .unmodeled := by
  refine wv_record_copyins_no_unmodeled reads1 _ i m ?_
  refine choose_bind_no_unmodeled _ _ i m (fun ds => ?_)
  refine emitSeq_no_unmodeled _ _ i m ?_
  exact wv_record_copyins_no_unmodeled _ _ i _ (pure_no_unmodeled _ i _)

theorem check_writev_complete_unmodeled (i : SyscallInput) (fd iov iovcnt : word)
    (m : Model) (eff : SyscallEffect)
    (Hs : writev_spec fd iov iovcnt i m .unmodeled) :
    check_writev i fd iov iovcnt eff m = .CheckUnmodeled := by
  unfold writev_spec at Hs
  simp only [check_writev]
  simp only [inputSpec, getModelSpec, bind_input_spec, bind_getModel] at Hs
  unfold writev_file_arm writev_ledger at Hs
  generalize hq : fd_lookup (m_fds m) fd = q at Hs ⊢
  cases q with
  | none =>
    try dsimp only at Hs ⊢
    exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)
  | some e =>
    cases e with
    | FdChannel ch =>
      try dsimp only at Hs ⊢
      by_cases hw : w_is0 ch = true
      · rw [ite_eq_left hw] at Hs ⊢
        exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)
      · rw [ite_eq_right hw] at Hs ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (wv_err_ret_no_unmodeled EFAULT i m))
        | ImpInval =>
          simp only [hiv] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (wv_err_ret_no_unmodeled EINVAL i m))
        | ImpOk iovs0 =>
          simp only [hiv] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at Hs ⊢
            exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
              (pure_no_unmodeled (mkEffect (BitVec.ofInt 64 0) [] []) i m))
          · rw [ite_eq_right htot] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
                (wv_err_ret_no_unmodeled EFAULT i m))
            · rw [ite_eq_right hbl] at Hs ⊢
              by_cases hae : addr_is_error_b (len_word bs) = true
              · rw [ite_eq_left hae] at Hs ⊢
              · rw [ite_eq_right hae] at Hs ⊢
                exact absurd Hs (wv_channel_leaf_no_unmodeled ch iovs0 i _ m bs)
    | FdFile p off =>
      try dsimp only at Hs ⊢
      exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)
    | FdFileW p off =>
      try dsimp only at Hs ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at Hs ⊢
        exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
          (wv_err_ret_no_unmodeled EFAULT i m))
      | ImpInval =>
        simp only [hiv] at Hs ⊢
        exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
          (wv_err_ret_no_unmodeled EINVAL i m))
      | ImpOk iovs0 =>
        simp only [hiv] at Hs ⊢
        try dsimp only at Hs ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (pure_no_unmodeled (mkEffect (BitVec.ofInt 64 0) [] []) i m))
        · rw [ite_eq_right htot] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
              (wv_err_ret_no_unmodeled EINVAL i m))
          · rw [ite_eq_right hpos] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
                (wv_err_ret_no_unmodeled EFAULT i m))
            · rw [ite_eq_right hbl] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs ⊢
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at Hs ⊢
                    try dsimp only at Hs ⊢
                  · rw [ite_eq_right hae] at Hs ⊢
                    exact absurd Hs
                      (wv_file_leaf_no_unmodeled (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs))
                        (fd_insert (m_fds m) fd (FdEntry.FdFileW p (off + len_word bs)))
                        _ _ (len_word bs) i m)
    | FdFileA p off =>
      try dsimp only at Hs ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at Hs ⊢
        exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
          (wv_err_ret_no_unmodeled EFAULT i m))
      | ImpInval =>
        simp only [hiv] at Hs ⊢
        exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
          (wv_err_ret_no_unmodeled EINVAL i m))
      | ImpOk iovs0 =>
        simp only [hiv] at Hs ⊢
        try dsimp only at Hs ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (pure_no_unmodeled (mkEffect (BitVec.ofInt 64 0) [] []) i m))
        · rw [ite_eq_right htot] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
              (wv_err_ret_no_unmodeled EINVAL i m))
          · rw [ite_eq_right hpos] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
                (wv_err_ret_no_unmodeled EFAULT i m))
            · rw [ite_eq_right hbl] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs ⊢
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hae : addr_is_error_b (len_word bs) = true
                · rw [ite_eq_left hae] at Hs ⊢
                  try dsimp only at Hs ⊢
                · rw [ite_eq_right hae] at Hs ⊢
                  exact absurd Hs
                    (wv_file_leaf_no_unmodeled (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs))
                      (fd_insert (m_fds m) fd (FdEntry.FdFileA p (append_new_pos data bs off)))
                      _ _ (len_word bs) i m)
    | FdFileRW p off =>
      try dsimp only at Hs ⊢
      cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
      | ImpFault =>
        simp only [hiv] at Hs ⊢
        exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
          (wv_err_ret_no_unmodeled EFAULT i m))
      | ImpInval =>
        simp only [hiv] at Hs ⊢
        exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
          (wv_err_ret_no_unmodeled EINVAL i m))
      | ImpOk iovs0 =>
        simp only [hiv] at Hs ⊢
        try dsimp only at Hs ⊢
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
        · rw [ite_eq_left htot] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (pure_no_unmodeled (mkEffect (BitVec.ofInt 64 0) [] []) i m))
        · rw [ite_eq_right htot] at Hs ⊢
          by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
          · rw [ite_eq_left hpos] at Hs ⊢
            exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
              (wv_err_ret_no_unmodeled EINVAL i m))
          · rw [ite_eq_right hpos] at Hs ⊢
            by_cases hbl : (bs.length == 0) = true
            · rw [ite_eq_left hbl] at Hs ⊢
              exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
                (wv_err_ret_no_unmodeled EFAULT i m))
            · rw [ite_eq_right hbl] at Hs ⊢
              cases hfs : Fs.fs_lookup (m_fs m) p with
              | none =>
                simp only [hfs] at Hs ⊢
              | some data =>
                simp only [hfs] at Hs ⊢
                try dsimp only at Hs ⊢
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                · rw [ite_eq_right hmg] at Hs ⊢
                  try dsimp only at Hs ⊢
                  by_cases hae : addr_is_error_b (len_word bs) = true
                  · rw [ite_eq_left hae] at Hs ⊢
                    try dsimp only at Hs ⊢
                  · rw [ite_eq_right hae] at Hs ⊢
                    exact absurd Hs
                      (wv_file_leaf_no_unmodeled (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs))
                        (fd_insert (m_fds m) fd (FdEntry.FdFileRW p (off + len_word bs)))
                        _ _ (len_word bs) i m)
    | FdDir =>
      try dsimp only at Hs ⊢
      exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)
    | FdSocket sk =>
      try dsimp only at Hs ⊢
    | FdPipe id w =>
      try dsimp only at Hs ⊢
      by_cases hw : (!w) = true
      · rw [ite_eq_left hw] at Hs ⊢
        exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)
      · rw [ite_eq_right hw] at Hs ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (wv_err_ret_no_unmodeled EFAULT i m))
        | ImpInval =>
          simp only [hiv] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (wv_err_ret_no_unmodeled EINVAL i m))
        | ImpOk iovs0 =>
          simp only [hiv] at Hs ⊢
          try dsimp only at Hs ⊢
          by_cases htot : (iovs_total (cap_iovecs iovs0) == 0) = true
          · rw [ite_eq_left htot] at Hs ⊢
            exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
              (pure_no_unmodeled (mkEffect (BitVec.ofInt 64 0) [] []) i m))
          · rw [ite_eq_right htot] at Hs ⊢
    | FdDevNull rd wr =>
      try dsimp only at Hs ⊢
      by_cases hwr : (!wr) = true
      · rw [ite_eq_left hwr] at Hs ⊢
        exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)
      · rw [ite_eq_right hwr] at Hs ⊢
        cases hiv : import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
        | ImpFault =>
          simp only [hiv] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (wv_err_ret_no_unmodeled EFAULT i m))
        | ImpInval =>
          simp only [hiv] at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (wv_err_ret_no_unmodeled EINVAL i m))
        | ImpOk iovs0 =>
          simp only [hiv] at Hs ⊢
          try dsimp only at Hs ⊢
          exact absurd Hs (wv_record_copyins_no_unmodeled _ _ i m
            (pure_no_unmodeled _ i m))
    | FdUrandom =>
      try dsimp only at Hs ⊢
      exact absurd Hs (wv_err_ret_no_unmodeled EBADF i m)

/- =========================================================================
   readv_imported (the acceptor of `ReadWrite.readv_imported`)
   ========================================================================= -/

/-- The channel readv's delivery stage, with the vectored ledger
    (`set_stdin` + per-byte events + the arbitrary write list). -/
private theorem seqSpec_set_stdin_deliver_writes (stdin : InputStream) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput)
    (m : Model) :
    seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m
      (.ok (mkEffect (len_word bs) writes []) (with_stdin stdin m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_stdin stdin m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_stdin stdin m, bs.map (event.ReadEv ch), [], rfl, rfl, by simp⟩

/-- The same on a socket's descriptor table. -/
private theorem seqSpec_set_fds_deliver_writes (fds : List (word × FdEntry))
    (ch : word) (writes : List (word × List byte)) (bs : List byte)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m
      (.ok (mkEffect (len_word bs) writes []) (with_fds fds m)
        (bs.map (event.ReadEv ch))) := by
  refine ⟨(), with_fds fds m, [], bs.map (event.ReadEv ch), rfl, ?_, rfl⟩
  refine ⟨(), with_fds fds m, bs.map (event.ReadEv ch), [], rfl, rfl, by simp⟩

theorem check_readv_imported_sound_ok (i : SyscallInput) (fd : word)
    (e : ReadableFd) (iovs : List (word × word)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_readv_imported i fd e iovs eff m = .CheckOk m' evs) :
    readv_imported fd e iovs i m i m (.ok eff m' evs) := by
  unfold check_readv_imported at H
  unfold readv_imported
  try dsimp only at H ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs) == 0) = true
  · rw [ite_eq_left hz] at H ⊢
    exact ret_only_ok_spec H i
  · rw [ite_eq_right hz] at H ⊢
    try dsimp only at H ⊢
    cases e with
    | RdChannel ch =>
      try dsimp only at H ⊢
      generalize hs : m_stdin m 0 = st at H ⊢
      cases st with
      | none =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | some b0 =>
        try dsimp only at H ⊢
        generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
          [BitVec.ofInt 8 0] = one at H ⊢
        cases one with
        | none =>
          try dsimp only at H ⊢
          exact ret_only_ok_spec H i
        | some one =>
          try dsimp only at H ⊢
          generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs))).1 = need
            at H ⊢
          cases need with
          | none =>
            try dsimp only at H
            exact nomatch H
          | some need =>
            try dsimp only at H ⊢
            obtain ⟨ret, writes, zs, us, cs, copyins⟩ := eff
            cases zs with
            | nil =>
              cases us with
              | nil =>
                cases cs with
                | nil =>
                  cases copyins with
                  | nil =>
                    try dsimp only at H ⊢
                    generalize hbs : (writes.map Prod.snd).flatten = bs at H ⊢
                    try dsimp only at H ⊢
                    generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs) bs = sc
                      at H ⊢
                    cases sc with
                    | none =>
                      try dsimp only at H
                      exact nomatch H
                    | some expected =>
                      try dsimp only at H ⊢
                      by_cases hgood : (bv_eqb ret (len_word bs)
                          && writes_eqb writes expected
                          && decide (1 ≤ (bs.length : Int))
                          && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs))
                          && listN_eqb (stream_take (m_stdin m) bs.length).1 bs) = true
                      · rw [ite_eq_left hgood] at H
                        cases H
                        have hgood' : bv_eqb ret (len_word bs) = true ∧
                            writes_eqb writes expected = true ∧
                            decide (1 ≤ (bs.length : Int)) = true ∧
                            decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs)) = true ∧
                            listN_eqb (stream_take (m_stdin m) bs.length).1 bs = true := by
                          simpa [Bool.and_eq_true, and_assoc] using hgood
                        obtain ⟨hret, hwr, hle1, hle2, hstream⟩ := hgood'
                        have hret' : ret = len_word bs := (Fs.bv_eqb_eq ret (len_word bs)).mp hret
                        have hwr' : writes = expected := (writes_eqb_eq writes expected).mp hwr
                        have hle1' : 1 ≤ (bs.length : Int) := of_decide_eq_true hle1
                        have hle2' : (bs.length : Int) ≤ iovs_total (cap_iovecs iovs) :=
                          of_decide_eq_true hle2
                        have hstream' : (stream_take (m_stdin m) bs.length).1 = bs :=
                          (listN_eqb_eq _ _).mp hstream
                        rw [hret', hwr']
                        refine ⟨bs, m, [], bs.map (event.ReadEv ch),
                          choose_ok _ bs i m ⟨hle1', hle2', hstream', ?_⟩, ?_, rfl⟩
                        · simp only [hsc]
                          simp
                        · simp only [hsc]
                          exact seqSpec_set_stdin_deliver_writes
                            (stream_take (m_stdin m) bs.length).2 ch expected bs i m
                      · rw [ite_eq_right hgood] at H
                        exact nomatch H
                  | cons _ _ =>
                    try dsimp only at H
                    exact nomatch H
                | cons _ _ =>
                  try dsimp only at H
                  exact nomatch H
              | cons _ _ =>
                try dsimp only at H
                exact nomatch H
            | cons _ _ =>
              try dsimp only at H
              exact nomatch H
    | RdFile p off =>
      try dsimp only at H ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at H
        try dsimp only at H
        exact nomatch H
      | some data =>
        simp only [hfs] at H ⊢
        try dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at H ⊢
          try dsimp only at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at H ⊢
          cases sc with
          | some writes =>
            try dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at H
              exact nomatch H
            · rw [ite_eq_right hae] at H ⊢
              try dsimp only at H ⊢
              obtain ⟨ret, writes', zs, us, cs, copyins⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases copyins with
                    | nil =>
                      try dsimp only at H ⊢
                      by_cases hgood : (bv_eqb ret (len_word (Fs.file_read data off
                          (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                          && writes_eqb writes' writes) = true
                      · rw [ite_eq_left hgood] at H
                        cases H
                        have hgood' : bv_eqb ret (len_word (Fs.file_read data off
                            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true ∧
                            writes_eqb writes' writes = true := by
                          simpa [Bool.and_eq_true] using hgood
                        obtain ⟨hret, hwr⟩ := hgood'
                        have hret' : ret = len_word (Fs.file_read data off
                            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) :=
                          (Fs.bv_eqb_eq _ _).mp hret
                        have hwr' : writes' = writes := (writes_eqb_eq _ _).mp hwr
                        rw [hret', hwr']
                        exact seqSpec_set_fds_pure_ok _
                          (mkEffect (len_word (Fs.file_read data off
                            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) writes []) i m
                      · rw [ite_eq_right hgood] at H
                        exact nomatch H
                    | cons _ _ =>
                      try dsimp only at H
                      exact nomatch H
                  | cons _ _ =>
                    try dsimp only at H
                    exact nomatch H
                | cons _ _ =>
                  try dsimp only at H
                  exact nomatch H
              | cons _ _ =>
                try dsimp only at H
                exact nomatch H
          | none =>
            try dsimp only at H ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at H ⊢
            cases one with
            | none =>
              try dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some one =>
              try dsimp only at H
              exact nomatch H
    | RdFileRW p off =>
      try dsimp only at H ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at H
        try dsimp only at H
        exact nomatch H
      | some data =>
        simp only [hfs] at H ⊢
        try dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at H ⊢
          try dsimp only at H ⊢
          exact ret_only_ok_spec H i
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at H ⊢
          cases sc with
          | some writes =>
            try dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at H
              exact nomatch H
            · rw [ite_eq_right hae] at H ⊢
              try dsimp only at H ⊢
              obtain ⟨ret, writes', zs, us, cs, copyins⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases copyins with
                    | nil =>
                      try dsimp only at H ⊢
                      by_cases hgood : (bv_eqb ret (len_word (Fs.file_read data off
                          (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                          && writes_eqb writes' writes) = true
                      · rw [ite_eq_left hgood] at H
                        cases H
                        have hgood' : bv_eqb ret (len_word (Fs.file_read data off
                            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true ∧
                            writes_eqb writes' writes = true := by
                          simpa [Bool.and_eq_true] using hgood
                        obtain ⟨hret, hwr⟩ := hgood'
                        have hret' : ret = len_word (Fs.file_read data off
                            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) :=
                          (Fs.bv_eqb_eq _ _).mp hret
                        have hwr' : writes' = writes := (writes_eqb_eq _ _).mp hwr
                        rw [hret', hwr']
                        exact seqSpec_set_fds_pure_ok _
                          (mkEffect (len_word (Fs.file_read data off
                            (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) writes []) i m
                      · rw [ite_eq_right hgood] at H
                        exact nomatch H
                    | cons _ _ =>
                      try dsimp only at H
                      exact nomatch H
                  | cons _ _ =>
                    try dsimp only at H
                    exact nomatch H
                | cons _ _ =>
                  try dsimp only at H
                  exact nomatch H
              | cons _ _ =>
                try dsimp only at H
                exact nomatch H
          | none =>
            try dsimp only at H ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at H ⊢
            cases one with
            | none =>
              try dsimp only at H ⊢
              exact ret_only_ok_spec H i
            | some one =>
              try dsimp only at H
              exact nomatch H
    | RdDir =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | RdSocket sk =>
      try dsimp only at H ⊢
      cases sk with
      | SkFresh =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | SkBound =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | SkListening =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
      | SkConnected peer ch rx =>
        try dsimp only at H ⊢
        generalize hrx : rx 0 = st at H ⊢
        cases st with
        | fin =>
          try dsimp only at H ⊢
          exact ret_only_ok_spec H i
        | rst =>
          try dsimp only at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret ECONNRESET)
              (with_fds (fd_insert (m_fds m) fd
                 (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [] m' evs).mp H
          exact seqSpec_set_fds_err_ret_ok _ ECONNRESET i m
        | timedOut =>
          try dsimp only at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret ETIMEDOUT)
              (with_fds (fd_insert (m_fds m) fd
                 (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [] m' evs).mp H
          exact seqSpec_set_fds_err_ret_ok _ ETIMEDOUT i m
        | cons b0 =>
          try dsimp only at H ⊢
          generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            [BitVec.ofInt 8 0] = one at H ⊢
          cases one with
          | none =>
            try dsimp only at H ⊢
            exact ret_only_ok_spec H i
          | some one =>
            try dsimp only at H ⊢
            generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              (net_take_z rx (iovs_total (cap_iovecs iovs))).1 = need at H ⊢
            cases need with
            | none =>
              try dsimp only at H
              exact nomatch H
            | some need =>
              try dsimp only at H ⊢
              obtain ⟨ret, writes, zs, us, cs, copyins⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases copyins with
                    | nil =>
                      try dsimp only at H ⊢
                      generalize hbs : (writes.map Prod.snd).flatten = bs at H ⊢
                      try dsimp only at H ⊢
                      generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs) bs = sc
                        at H ⊢
                      cases sc with
                      | none =>
                        try dsimp only at H
                        exact nomatch H
                      | some expected =>
                        try dsimp only at H ⊢
                        by_cases hgood : (bv_eqb ret (len_word bs)
                            && writes_eqb writes expected
                            && decide (1 ≤ (bs.length : Int))
                            && decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs))
                            && listN_eqb (net_take rx bs.length).1 bs) = true
                        · rw [ite_eq_left hgood] at H
                          cases H
                          have hgood' : bv_eqb ret (len_word bs) = true ∧
                              writes_eqb writes expected = true ∧
                              decide (1 ≤ (bs.length : Int)) = true ∧
                              decide ((bs.length : Int) ≤ iovs_total (cap_iovecs iovs)) = true ∧
                              listN_eqb (net_take rx bs.length).1 bs = true := by
                            simpa [Bool.and_eq_true, and_assoc] using hgood
                          obtain ⟨hret, hwr, hle1, hle2, hstream⟩ := hgood'
                          have hret' : ret = len_word bs := (Fs.bv_eqb_eq _ _).mp hret
                          have hwr' : writes = expected := (writes_eqb_eq _ _).mp hwr
                          have hle1' : 1 ≤ (bs.length : Int) := of_decide_eq_true hle1
                          have hle2' : (bs.length : Int) ≤ iovs_total (cap_iovecs iovs) :=
                            of_decide_eq_true hle2
                          have hstream' : (net_take rx bs.length).1 = bs :=
                            (listN_eqb_eq _ _).mp hstream
                          rw [hret', hwr']
                          refine ⟨bs, m, [], bs.map (event.ReadEv ch),
                            choose_ok _ bs i m ⟨hle1', hle2', hstream', ?_⟩, ?_, rfl⟩
                          · simp only [hsc]
                            simp
                          · simp only [hsc]
                            exact seqSpec_set_fds_deliver_writes
                              (fd_insert (m_fds m) fd
                                 (FdEntry.FdSocket (SockState.SkConnected peer ch
                                    (net_take rx bs.length).2))) ch expected bs i m
                        · rw [ite_eq_right hgood] at H
                          exact nomatch H
                    | cons _ _ =>
                      try dsimp only at H
                      exact nomatch H
                  | cons _ _ =>
                    try dsimp only at H
                    exact nomatch H
                | cons _ _ =>
                  try dsimp only at H
                  exact nomatch H
              | cons _ _ =>
                try dsimp only at H
                exact nomatch H
      | SkReset peer ch =>
        try dsimp only at H ⊢
        exact ret_only_ok_spec H i
    | RdPipe id =>
      try dsimp only at H
      exact nomatch H
    | RdDevNull =>
      try dsimp only at H ⊢
      exact ret_only_ok_spec H i
    | RdUrandom =>
      try dsimp only at H
      exact nomatch H

theorem check_readv_imported_sound_unmodeled (i : SyscallInput) (fd : word)
    (e : ReadableFd) (iovs : List (word × word)) (eff : SyscallEffect)
    (m : Model)
    (H : check_readv_imported i fd e iovs eff m = .CheckUnmodeled) :
    readv_imported fd e iovs i m i m .unmodeled := by
  unfold check_readv_imported at H
  unfold readv_imported
  try dsimp only at H ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs) == 0) = true
  · rw [ite_eq_left hz] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
  · rw [ite_eq_right hz] at H ⊢
    try dsimp only at H ⊢
    cases e with
    | RdChannel ch =>
      try dsimp only at H ⊢
      generalize hs : m_stdin m 0 = st at H ⊢
      cases st with
      | none =>
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      | some b0 =>
        generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
          [BitVec.ofInt 8 0] = one at H ⊢
        cases one with
        | none =>
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        | some one =>
          generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs))).1 = need
            at H ⊢
          cases need with
          | none =>
            unfold readv_buf_gap
            exact unmodeled_intro i m
          | some need =>
            try dsimp only at H ⊢
            obtain ⟨ret, writes, zs, us, cs, copyins⟩ := eff
            cases zs with
            | nil =>
              cases us with
              | nil =>
                cases cs with
                | nil =>
                  cases copyins with
                  | nil =>
                    by_cases hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
                        ((writes.map Prod.snd).flatten) = none
                    · simp only [hsc] at H
                      try simp only [] at H
                      exact nomatch H
                    · cases hsc' : scatter_iovecs i.in_wmem (cap_iovecs iovs)
                        ((writes.map Prod.snd).flatten) with
                      | none =>
                        rw [hsc'] at hsc
                        exact absurd rfl hsc
                      | some expected =>
                        simp only [hsc'] at H
                        try simp only [] at H
                        by_cases hg : (bv_eqb ret (len_word (writes.map Prod.snd).flatten)
                            && writes_eqb writes expected
                            && decide (1 ≤ ((writes.map Prod.snd).flatten.length : Int))
                            && decide (((writes.map Prod.snd).flatten.length : Int) ≤ iovs_total (cap_iovecs iovs))
                            && listN_eqb (stream_take (m_stdin m) (writes.map Prod.snd).flatten.length).1 (writes.map Prod.snd).flatten) = true
                        · rw [ite_eq_left hg] at H
                          exact nomatch H
                        · rw [ite_eq_right hg] at H
                          exact nomatch H
                  | cons _ _ =>
                    try simp only [] at H
                    exact nomatch H
                | cons _ _ =>
                  try simp only [] at H
                  exact nomatch H
              | cons _ _ =>
                try simp only [] at H
                exact nomatch H
            | cons _ _ =>
              try simp only [] at H
              exact nomatch H
    | RdFile p off =>
      try dsimp only at H ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        try simp only [hfs] at H ⊢
        unfold readv_buf_gap
        exact unmodeled_intro i m
      | some data =>
        try simp only [hfs] at H ⊢
        try dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at H ⊢
          cases sc with
          | some writes =>
            try dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
            · rw [ite_eq_right hae] at H ⊢
              try dsimp only at H ⊢
              obtain ⟨ret, writes', zs, us, cs, copyins⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases copyins with
                    | nil =>
                      try simp only [] at H
                      by_cases hg : (bv_eqb ret (len_word (Fs.file_read data off
                          (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                          && writes_eqb writes' writes) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    | cons _ _ =>
                      try simp only [] at H
                      exact nomatch H
                  | cons _ _ =>
                    try simp only [] at H
                    exact nomatch H
                | cons _ _ =>
                  try simp only [] at H
                  exact nomatch H
              | cons _ _ =>
                try simp only [] at H
                exact nomatch H
          | none =>
            try dsimp only at H ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at H ⊢
            cases one with
            | none =>
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | some one =>
              unfold readv_buf_gap
              exact unmodeled_intro i m
    | RdFileRW p off =>
      try dsimp only at H ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at H ⊢
        unfold readv_buf_gap
        exact unmodeled_intro i m
      | some data =>
        simp only [hfs] at H ⊢
        try dsimp only at H ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hpos] at H ⊢
          try dsimp only at H ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at H ⊢
          cases sc with
          | some writes =>
            try dsimp only at H ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at H ⊢
              unfold readv_buf_gap
              exact unmodeled_intro i m
            · rw [ite_eq_right hae] at H ⊢
              try dsimp only at H ⊢
              obtain ⟨ret, writes', zs, us, cs, copyins⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases copyins with
                    | nil =>
                      try simp only [] at H
                      by_cases hg : (bv_eqb ret (len_word (Fs.file_read data off
                          (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                          && writes_eqb writes' writes) = true
                      · rw [ite_eq_left hg] at H
                        exact nomatch H
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                    | cons _ _ =>
                      try simp only [] at H
                      exact nomatch H
                  | cons _ _ =>
                    try simp only [] at H
                    exact nomatch H
                | cons _ _ =>
                  try simp only [] at H
                  exact nomatch H
              | cons _ _ =>
                try simp only [] at H
                exact nomatch H
          | none =>
            try dsimp only at H ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at H ⊢
            cases one with
            | none =>
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
            | some one =>
              unfold readv_buf_gap
              exact unmodeled_intro i m
    | RdDir =>
      try dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
    | RdSocket sk =>
      try dsimp only at H ⊢
      cases sk with
      | SkFresh =>
        try dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
      | SkBound =>
        try dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
      | SkListening =>
        try dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
      | SkConnected peer ch rx =>
        try dsimp only at H ⊢
        generalize hrx : rx 0 = st at H ⊢
        cases st with
        | fin =>
          exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
        | rst =>
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ECONNRESET)
            (with_fds (fd_insert (m_fds m) fd
               (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])
        | timedOut =>
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ETIMEDOUT)
            (with_fds (fd_insert (m_fds m) fd
               (FdEntry.FdSocket (SockState.SkReset peer ch))) m) [])
        | cons b0 =>
          generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            [BitVec.ofInt 8 0] = one at H ⊢
          cases one with
          | none =>
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          | some one =>
            generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              (net_take_z rx (iovs_total (cap_iovecs iovs))).1 = need at H ⊢
            cases need with
            | none =>
              unfold readv_buf_gap
              exact unmodeled_intro i m
            | some need =>
              try dsimp only at H ⊢
              obtain ⟨ret, writes, zs, us, cs, copyins⟩ := eff
              cases zs with
              | nil =>
                cases us with
                | nil =>
                  cases cs with
                  | nil =>
                    cases copyins with
                    | nil =>
                      by_cases hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
                          ((writes.map Prod.snd).flatten) = none
                      · simp only [hsc] at H
                        try simp only [] at H
                        exact nomatch H
                      · cases hsc' : scatter_iovecs i.in_wmem (cap_iovecs iovs)
                          ((writes.map Prod.snd).flatten) with
                        | none =>
                          simp only [hsc'] at hsc
                          exact absurd trivial hsc
                        | some expected =>
                          simp only [hsc'] at H
                          try simp only [] at H
                          by_cases hg : (bv_eqb ret (len_word (writes.map Prod.snd).flatten)
                              && writes_eqb writes expected
                              && decide (1 ≤ ((writes.map Prod.snd).flatten.length : Int))
                              && decide (((writes.map Prod.snd).flatten.length : Int) ≤ iovs_total (cap_iovecs iovs))
                              && listN_eqb (net_take rx (writes.map Prod.snd).flatten.length).1 (writes.map Prod.snd).flatten) = true
                          · rw [ite_eq_left hg] at H
                            exact nomatch H
                          · rw [ite_eq_right hg] at H
                            exact nomatch H
                    | cons _ _ =>
                      try simp only [] at H
                      exact nomatch H
                  | cons _ _ =>
                    try simp only [] at H
                    exact nomatch H
                | cons _ _ =>
                  try simp only [] at H
                  exact nomatch H
              | cons _ _ =>
                try simp only [] at H
                exact nomatch H
      | SkReset peer ch =>
        try dsimp only at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | RdPipe id =>
      try dsimp only at H ⊢
      unfold readv_buf_gap
      exact unmodeled_intro i m
    | RdDevNull =>
      try dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | RdUrandom =>
      try dsimp only at H ⊢
      unfold readv_buf_gap
      exact unmodeled_intro i m

/-- A delivery stage written as `set_* ;; emit ;; pure` cannot
    decline, at any scattered value; the fail-closed arm is a bare
    `choose (fun _ => False)`, which cannot either. -/
private theorem readv_scatter_deliver_no_unmodeled (f : Model → Model) (ch : word)
    (iovs : List (word × word)) (i : SyscallInput) (m : Model) :
    ∀ bs : List byte,
      ¬ (match scatter_iovecs i.in_wmem (cap_iovecs iovs) bs with
         | some writes => seqSpec (modifySpec f)
             (seqSpec (emit (bs.map (event.ReadEv ch)))
               (pure (mkEffect (len_word bs) writes [])))
         | none => choose (fun _ => False)) i m .unmodeled := by
  intro bs
  by_cases h : scatter_iovecs i.in_wmem (cap_iovecs iovs) bs = none
  · rw [h]
    exact choose_no_unmodeled _ i m
  · cases h' : scatter_iovecs i.in_wmem (cap_iovecs iovs) bs with
    | none =>
      rw [h'] at h
      exact absurd rfl h
    | some writes =>
      simp only []
      exact deliverSeq_no_unmodeled f _ _ i m

theorem check_readv_imported_complete_unmodeled (i : SyscallInput) (fd : word)
    (e : ReadableFd) (iovs : List (word × word)) (m : Model)
    (eff : SyscallEffect)
    (Hs : readv_imported fd e iovs i m i m .unmodeled) :
    check_readv_imported i fd e iovs eff m = .CheckUnmodeled := by
  unfold readv_imported at Hs
  unfold check_readv_imported
  try dsimp only at Hs ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs) == 0) = true
  · rw [ite_eq_left hz] at Hs ⊢
    try simp only [] at Hs
    exact absurd Hs (pure_no_unmodeled _ i m)
  · rw [ite_eq_right hz] at Hs ⊢
    try dsimp only at Hs ⊢
    cases e with
    | RdChannel ch =>
      try dsimp only at Hs ⊢
      generalize hs : m_stdin m 0 = st at Hs ⊢
      cases st with
      | none =>
        try simp only [] at Hs
        exact absurd Hs (pure_no_unmodeled _ i m)
      | some b0 =>
        try simp only [] at Hs ⊢
        generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
          [BitVec.ofInt 8 0] = one at Hs ⊢
        cases one with
        | none =>
          try simp only [] at Hs
          exact absurd Hs (wv_err_ret_no_unmodeled EFAULT i m)
        | some one =>
          try simp only [] at Hs ⊢
          generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs))).1 = need
            at Hs ⊢
          cases need with
          | none =>
            try simp only [] at Hs ⊢
            rfl
          | some need =>
            try simp only [] at Hs ⊢
            exact absurd Hs (choose_bind_no_unmodeled _ _ i m
              (fun bs => readv_scatter_deliver_no_unmodeled
                (with_stdin (stream_take (m_stdin m) bs.length).2) ch iovs i m bs))
    | RdFile p off =>
      try dsimp only at Hs ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at Hs ⊢
        rfl
      | some data =>
        simp only [hfs] at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          exact absurd Hs (wv_err_ret_no_unmodeled EINVAL i m)
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at Hs ⊢
          cases sc with
          | some writes =>
            try simp only [] at Hs ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at Hs ⊢
              rfl
            · rw [ite_eq_right hae] at Hs ⊢
              exact absurd Hs (seqSpec_pure_no_unmodeled
                (set_fds (fd_insert (m_fds m) fd
                   (FdEntry.FdFile p (off + len_word (Fs.file_read data off
                      (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))))))
                _ i m (modifySpec_no_unmodeled _ i m))
          | none =>
            try simp only [] at Hs ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at Hs ⊢
            cases one with
            | none =>
              try simp only [] at Hs
              exact absurd Hs (wv_err_ret_no_unmodeled EFAULT i m)
            | some one =>
              try simp only [] at Hs ⊢
              rfl
    | RdFileRW p off =>
      try dsimp only at Hs ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at Hs ⊢
        rfl
      | some data =>
        simp only [hfs] at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          exact absurd Hs (wv_err_ret_no_unmodeled EINVAL i m)
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at Hs ⊢
          cases sc with
          | some writes =>
            try simp only [] at Hs ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at Hs ⊢
              rfl
            · rw [ite_eq_right hae] at Hs ⊢
              exact absurd Hs (seqSpec_pure_no_unmodeled
                (set_fds (fd_insert (m_fds m) fd
                   (FdEntry.FdFileRW p (off + len_word (Fs.file_read data off
                      (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))))))
                _ i m (modifySpec_no_unmodeled _ i m))
          | none =>
            try simp only [] at Hs ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at Hs ⊢
            cases one with
            | none =>
              try simp only [] at Hs
              exact absurd Hs (wv_err_ret_no_unmodeled EFAULT i m)
            | some one =>
              try simp only [] at Hs ⊢
              rfl
    | RdDir =>
      try dsimp only at Hs
      exact absurd Hs (wv_err_ret_no_unmodeled EISDIR i m)
    | RdSocket sk =>
      try dsimp only at Hs ⊢
      cases sk with
      | SkFresh =>
        try dsimp only at Hs
        exact absurd Hs (wv_err_ret_no_unmodeled ENOTCONN i m)
      | SkBound =>
        try dsimp only at Hs
        exact absurd Hs (wv_err_ret_no_unmodeled ENOTCONN i m)
      | SkListening =>
        try dsimp only at Hs
        exact absurd Hs (wv_err_ret_no_unmodeled ENOTCONN i m)
      | SkConnected peer ch rx =>
        try dsimp only at Hs ⊢
        generalize hrx : rx 0 = st at Hs ⊢
        cases st with
        | fin =>
          try simp only [] at Hs
          exact absurd Hs (pure_no_unmodeled _ i m)
        | rst =>
          try simp only [] at Hs ⊢
          exact absurd Hs (seqSpec_no_unmodeled (set_fds (fd_insert (m_fds m) fd
              (FdEntry.FdSocket (SockState.SkReset peer ch))))
            _ i m (modifySpec_no_unmodeled _ i m)
            (fun _ m1 _ _ => wv_err_ret_no_unmodeled ECONNRESET i m1))
        | timedOut =>
          try simp only [] at Hs ⊢
          exact absurd Hs (seqSpec_no_unmodeled (set_fds (fd_insert (m_fds m) fd
              (FdEntry.FdSocket (SockState.SkReset peer ch))))
            _ i m (modifySpec_no_unmodeled _ i m)
            (fun _ m1 _ _ => wv_err_ret_no_unmodeled ETIMEDOUT i m1))
        | cons b0 =>
          try simp only [] at Hs ⊢
          generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            [BitVec.ofInt 8 0] = one at Hs ⊢
          cases one with
          | none =>
            try simp only [] at Hs
            exact absurd Hs (wv_err_ret_no_unmodeled EFAULT i m)
          | some one =>
            try simp only [] at Hs ⊢
            generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              (net_take_z rx (iovs_total (cap_iovecs iovs))).1 = need at Hs ⊢
            cases need with
            | none =>
              try simp only [] at Hs ⊢
              rfl
            | some need =>
              try simp only [] at Hs ⊢
              exact absurd Hs (choose_bind_no_unmodeled _ _ i m
                (fun bs => readv_scatter_deliver_no_unmodeled
                  (with_fds (fd_insert (m_fds m) fd
                     (FdEntry.FdSocket (SockState.SkConnected peer ch
                        (net_take rx bs.length).2)))) ch iovs i m bs))
      | SkReset peer ch =>
        try dsimp only at Hs
        exact absurd Hs (pure_no_unmodeled _ i m)
    | RdPipe id =>
      try dsimp only at Hs ⊢
      rfl
    | RdDevNull =>
      try dsimp only at Hs
      exact absurd Hs (pure_no_unmodeled _ i m)
    | RdUrandom =>
      try dsimp only at Hs ⊢
      rfl

/-- `readv_buf_gap` admits no accepted outcome. -/
private theorem wv_readv_gap_no_ok (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : readv_buf_gap i m (.ok eff m' evs)) : False := by
  unfold readv_buf_gap LinuxSem.LinuxProcessSem.unmodeled at H
  exact nomatch H

/-- Invert the channel delivery stage of a vectored read. -/
private theorem wv_stdin_deliver_writes_inv (stdin : InputStream) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_stdin stdin)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) writes [] ∧ m' = with_stdin stdin m ∧
      evs = bs.map (event.ReadEv ch) := by
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

/-- The same on a socket's descriptor table. -/
private theorem wv_fds_deliver_writes_inv (fds : List (word × FdEntry)) (ch : word)
    (writes : List (word × List byte)) (bs : List byte) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (set_fds fds)
      (seqSpec (emit (bs.map (event.ReadEv ch)))
        (pure (mkEffect (len_word bs) writes []))) i m (.ok eff m' evs)) :
    eff = mkEffect (len_word bs) writes [] ∧ m' = with_fds fds m ∧
      evs = bs.map (event.ReadEv ch) := by
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

theorem check_readv_imported_complete_ok (i : SyscallInput) (fd : word)
    (e : ReadableFd) (iovs : List (word × word)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (Hs : readv_imported fd e iovs i m i m (.ok eff m' evs)) :
    check_readv_imported i fd e iovs eff m = .CheckOk m' evs := by
  unfold readv_imported at Hs
  unfold check_readv_imported
  try dsimp only at Hs ⊢
  by_cases hz : (iovs_total (cap_iovecs iovs) == 0) = true
  · rw [ite_eq_left hz] at Hs ⊢
    obtain ⟨heff, hm', hevs⟩ :=
      wv_ret_only_outcome (BitVec.ofInt 64 0) i m eff m' evs Hs
    rw [heff, hm', hevs]
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hz] at Hs ⊢
    try dsimp only at Hs ⊢
    cases e with
    | RdChannel ch =>
      try dsimp only at Hs ⊢
      generalize hs : m_stdin m 0 = st at Hs ⊢
      cases st with
      | none =>
        try simp only [] at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ :=
          wv_ret_only_outcome (BitVec.ofInt 64 0) i m eff m' evs Hs
        rw [heff, hm', hevs]
        simp [check_ret_only, bv_eqb_refl]
      | some b0 =>
        try simp only [] at Hs ⊢
        generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
          [BitVec.ofInt 8 0] = one at Hs ⊢
        cases one with
        | none =>
          try simp only [] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_outcome (errno_ret EFAULT) i m eff m' evs Hs
          rw [heff, hm', hevs]
          simp [check_ret_only, bv_eqb_refl]
        | some one =>
          try simp only [] at Hs ⊢
          generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (stream_take_z (m_stdin m) (iovs_total (cap_iovecs iovs))).1 = need
            at Hs ⊢
          cases need with
          | none =>
            try simp only [] at Hs
            exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
          | some need =>
            try simp only [] at Hs ⊢
            obtain ⟨ds, hP, hk⟩ :=
              choose_bind_ok_inv _ _ i m eff m' evs Hs
            obtain ⟨hP1, hP2, hP3, hPne⟩ := hP
            cases hsc' : scatter_iovecs i.in_wmem (cap_iovecs iovs) ds with
            | none =>
              rw [hsc'] at hPne
              exact absurd rfl hPne
            | some writes =>
              simp only [hsc'] at hk
              obtain ⟨heff, hm', hevs⟩ :=
                wv_stdin_deliver_writes_inv _ ch writes ds i m eff m' evs hk
              rw [heff, hm', hevs]
              have hcat : (writes.map Prod.snd).flatten = ds :=
                scatter_iovecs_concat _ _ _ _ hsc'
              simp only [hcat]
              rw [hsc']
              try simp only []
              have hg : (bv_eqb (len_word ds) (len_word ds) && writes_eqb writes writes
                  && decide (1 ≤ (ds.length : Int))
                  && decide ((ds.length : Int) ≤ iovs_total (cap_iovecs iovs))
                  && listN_eqb (stream_take (m_stdin m) ds.length).1 ds) = true := by
                simp [bv_eqb_refl, writes_eqb_eq, listN_eqb_eq, hP1, hP2, hP3]
              rw [ite_eq_left hg]
    | RdFile p off =>
      try dsimp only at Hs ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at Hs
        exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
      | some data =>
        simp only [hfs] at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_outcome (errno_ret EINVAL) i m eff m' evs Hs
          rw [heff, hm', hevs]
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at Hs ⊢
          cases sc with
          | some writes =>
            try simp only [] at Hs ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at Hs
              exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
            · rw [ite_eq_right hae] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) writes [])
                  i m eff m' evs Hs
              rw [heff, hm', hevs]
              try simp only []
              have hg : (bv_eqb (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                  (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                  && writes_eqb writes writes) = true := by
                simp [bv_eqb_refl, writes_eqb_eq]
              rw [ite_eq_left hg]
          | none =>
            try simp only [] at Hs ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at Hs ⊢
            cases one with
            | none =>
              try simp only [] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                wv_ret_only_outcome (errno_ret EFAULT) i m eff m' evs Hs
              rw [heff, hm', hevs]
              simp [check_ret_only, bv_eqb_refl]
            | some one =>
              try simp only [] at Hs
              exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
    | RdFileRW p off =>
      try dsimp only at Hs ⊢
      cases hfs : Fs.fs_lookup (m_fs m) p with
      | none =>
        simp only [hfs] at Hs
        exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
      | some data =>
        simp only [hfs] at Hs ⊢
        try dsimp only at Hs ⊢
        by_cases hpos : rw_pos_einvalb off (iovs_total (cap_iovecs iovs)) = true
        · rw [ite_eq_left hpos] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_outcome (errno_ret EINVAL) i m eff m' evs Hs
          rw [heff, hm', hevs]
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hpos] at Hs ⊢
          try dsimp only at Hs ⊢
          generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            (Fs.file_read data off (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))) = sc
            at Hs ⊢
          cases sc with
          | some writes =>
            try simp only [] at Hs ⊢
            by_cases hae : addr_is_error_b (len_word (Fs.file_read data off
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) = true
            · rw [ite_eq_left hae] at Hs
              exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
            · rw [ite_eq_right hae] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                seqSpec_set_fds_pure_ok_inv _
                  (mkEffect (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs))))) writes [])
                  i m eff m' evs Hs
              rw [heff, hm', hevs]
              try simp only []
              have hg : (bv_eqb (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                  (len_word (Fs.file_read data off
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs)))))
                  && writes_eqb writes writes) = true := by
                simp [bv_eqb_refl, writes_eqb_eq]
              rw [ite_eq_left hg]
          | none =>
            try simp only [] at Hs ⊢
            generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              [BitVec.ofInt 8 0] = one at Hs ⊢
            cases one with
            | none =>
              try simp only [] at Hs ⊢
              obtain ⟨heff, hm', hevs⟩ :=
                wv_ret_only_outcome (errno_ret EFAULT) i m eff m' evs Hs
              rw [heff, hm', hevs]
              simp [check_ret_only, bv_eqb_refl]
            | some one =>
              try simp only [] at Hs
              exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
    | RdDir =>
      try dsimp only at Hs ⊢
      obtain ⟨heff, hm', hevs⟩ :=
        wv_ret_only_outcome (errno_ret EISDIR) i m eff m' evs Hs
      rw [heff, hm', hevs]
      simp [check_ret_only, bv_eqb_refl]
    | RdSocket sk =>
      try dsimp only at Hs ⊢
      cases sk with
      | SkFresh =>
        try dsimp only at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ :=
          wv_ret_only_outcome (errno_ret ENOTCONN) i m eff m' evs Hs
        rw [heff, hm', hevs]
        simp [check_ret_only, bv_eqb_refl]
      | SkBound =>
        try dsimp only at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ :=
          wv_ret_only_outcome (errno_ret ENOTCONN) i m eff m' evs Hs
        rw [heff, hm', hevs]
        simp [check_ret_only, bv_eqb_refl]
      | SkListening =>
        try dsimp only at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ :=
          wv_ret_only_outcome (errno_ret ENOTCONN) i m eff m' evs Hs
        rw [heff, hm', hevs]
        simp [check_ret_only, bv_eqb_refl]
      | SkConnected peer ch rx =>
        try dsimp only at Hs ⊢
        generalize hrx : rx 0 = st at Hs ⊢
        cases st with
        | fin =>
          try simp only [] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            wv_ret_only_outcome (BitVec.ofInt 64 0) i m eff m' evs Hs
          rw [heff, hm', hevs]
          simp [check_ret_only, bv_eqb_refl]
        | rst =>
          try simp only [] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            seqSpec_set_fds_err_ret_ok_inv _ ECONNRESET i m eff m' evs Hs
          rw [heff, hm', hevs]
          simp [check_ret_only, bv_eqb_refl]
        | timedOut =>
          try simp only [] at Hs ⊢
          obtain ⟨heff, hm', hevs⟩ :=
            seqSpec_set_fds_err_ret_ok_inv _ ETIMEDOUT i m eff m' evs Hs
          rw [heff, hm', hevs]
          simp [check_ret_only, bv_eqb_refl]
        | cons b0 =>
          try simp only [] at Hs ⊢
          generalize hone : scatter_iovecs i.in_wmem (cap_iovecs iovs)
            [BitVec.ofInt 8 0] = one at Hs ⊢
          cases one with
          | none =>
            try simp only [] at Hs ⊢
            obtain ⟨heff, hm', hevs⟩ :=
              wv_ret_only_outcome (errno_ret EFAULT) i m eff m' evs Hs
            rw [heff, hm', hevs]
            simp [check_ret_only, bv_eqb_refl]
          | some one =>
            try simp only [] at Hs ⊢
            generalize hneed : scatter_iovecs i.in_wmem (cap_iovecs iovs)
              (net_take_z rx (iovs_total (cap_iovecs iovs))).1 = need at Hs ⊢
            cases need with
            | none =>
              try simp only [] at Hs
              exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
            | some need =>
              try simp only [] at Hs ⊢
              obtain ⟨ds, hP, hk⟩ :=
                choose_bind_ok_inv _ _ i m eff m' evs Hs
              obtain ⟨hP1, hP2, hP3, hPne⟩ := hP
              cases hsc' : scatter_iovecs i.in_wmem (cap_iovecs iovs) ds with
              | none =>
                rw [hsc'] at hPne
                exact absurd rfl hPne
              | some writes =>
                simp only [hsc'] at hk
                obtain ⟨heff, hm', hevs⟩ :=
                  wv_fds_deliver_writes_inv _ ch writes ds i m eff m' evs hk
                rw [heff, hm', hevs]
                have hcat : (writes.map Prod.snd).flatten = ds :=
                  scatter_iovecs_concat _ _ _ _ hsc'
                simp only [hcat]
                rw [hsc']
                try simp only []
                have hg : (bv_eqb (len_word ds) (len_word ds) && writes_eqb writes writes
                    && decide (1 ≤ (ds.length : Int))
                    && decide ((ds.length : Int) ≤ iovs_total (cap_iovecs iovs))
                    && listN_eqb (net_take rx ds.length).1 ds) = true := by
                  simp [bv_eqb_refl, writes_eqb_eq, listN_eqb_eq, hP1, hP2, hP3]
                rw [ite_eq_left hg]
      | SkReset peer ch =>
        try dsimp only at Hs ⊢
        obtain ⟨heff, hm', hevs⟩ :=
          wv_ret_only_outcome (BitVec.ofInt 64 0) i m eff m' evs Hs
        rw [heff, hm', hevs]
        simp [check_ret_only, bv_eqb_refl]
    | RdPipe id =>
      try dsimp only at Hs
      exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)
    | RdDevNull =>
      try dsimp only at Hs ⊢
      obtain ⟨heff, hm', hevs⟩ :=
        wv_ret_only_outcome (BitVec.ofInt 64 0) i m eff m' evs Hs
      rw [heff, hm', hevs]
      simp [check_ret_only, bv_eqb_refl]
    | RdUrandom =>
      try dsimp only at Hs
      exact False.elim (wv_readv_gap_no_ok i m eff m' evs Hs)

end LinuxSem.Checks.Sys.Fs.ReadWrite
