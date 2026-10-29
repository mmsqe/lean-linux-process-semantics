/-
  * LinuxProcessSem.Checks.Sys.Fs.Pipe — the pipe2 (59) checker, and its proofs

  Answers to Linux [fs/pipe.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  `Checks.Sys.Prelude` supplies every helper this arm uses
  ([check_ret_only], [errno_ret_in], [bv_eqb], [listN_eqb],
  [read_bytes_map]) — or the `State`/`Fs` layer under it does — so
  `Checks.Sys.Fs.ReadWrite` is not imported.  Nothing here needs it.

  Flags are read UNSIGNED (`(flags.toNat : Int)`), the mask difference is
  `z_ldiff`, `FdPipe id b` is `FdEntry.FdPipe id b`, the spec monad `Sys A`
  is `SysSpec A`, a witness answers with `Outcome A Model event`, and the
  checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`).  An effect literal is the anonymous constructor
  pattern `⟨r, ws, [], [], [], []⟩` over `SyscallEffect`.

  The proofs run a `cases` chain over the effect's six fields and close each
  dead list shape with `exact nomatch H`.  The scratch rules [hall],
  [inv_ok] and [sys_unfold] of `Checks.Sys.Prelude` are not what these
  proofs use: the four theorems below generalize the CONCLUSION to an opaque
  `Q` (the header of `Checks/Sys/Fs/File.lean` records why — a
  `by_cases`/`cases` on an `if` test that narrows a word loops when the same
  test is also in the target), split on the very same tests the checker and
  the spec share, and rewrite back to the spec only at the leaves with
  `rw [← hP]`.  `cases h : e` yields the equation but does not rewrite the
  other hypotheses — a Lean `cases` abstracts the scrutinee in the TARGET
  only — so every branch rewrites H with `h` explicitly.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Pipe

namespace LinuxSem.Checks.Sys.Fs.Pipe

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Pipe
open LinuxSem.Checks.Sys.Prelude

/- =========================================================================
   The pipe2 descriptors and the model it leaves behind
   ========================================================================= -/

/-- The read-end descriptor `pipe2` hands out: the lowest free number in
    the model's fd table (`__do_pipe_flags`' first `get_unused_fd_flags`,
    fs/pipe.c:994-1006, v6.18.46).  Named so the acceptor's success test
    and the proofs below talk about the same term — and so that term is
    the one `Sys.Fs.Pipe.pipe2_spec`'s `lowest_fd` chooses. -/
def pipe2_fdr (m : Model) : word := alloc_fd (m_fds m)

/-- The fd table after the READ end is reserved: the table that the write
    end's allocation scans, which is why `pipe2_fdw` is one higher than
    `pipe2_fdr` on a fresh table. -/
def pipe2_fds1 (m : Model) (id : word) : List (word × FdEntry) :=
  fd_insert (m_fds m) (pipe2_fdr m) (FdEntry.FdPipe id false)

/-- The write-end descriptor: the lowest free number ABOVE the reserved
    read end. -/
def pipe2_fdw (m : Model) (id : word) : word :=
  alloc_fd (pipe2_fds1 m id)

/-- The model a successful `pipe2` leaves: both descriptors installed (the
    read end first) and the pipe an empty queue.  The fd table is rebuilt
    before the pipe table, exactly as `Sys.Fs.Pipe.pipe2_spec`'s two
    `modify`s do — the two subsystems are disjoint, so the order is
    immaterial, but the terms must agree for the proof to close by
    reduction. -/
def pipe2_model (m : Model) (id : word) : Model :=
  with_pipes (pipe_insert (m_pipes m) id ([], (0 : Int)))
    (with_fds (fd_insert (pipe2_fds1 m id) (pipe2_fdw m id) (FdEntry.FdPipe id true)) m)

/- =========================================================================
   The checker
   ========================================================================= -/

/-- [Sys.Fs.Pipe.pipe2_spec] as an acceptor.  Two admissible shapes on the
    branches that can succeed — the injected environment errno, and the
    single 8-byte copy-out — so the effect's own write list is what picks
    between them. -/
def check_pipe2 (i : SyscallInput) (fildes flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(w_is0 flags) then .CheckUnmodeled
  else
  let id := pipe_new_id (m_pipes m)
  match pipe_lookup (m_pipes m) id with
  | some _ => .CheckUnmodeled
  | none =>
      if !(access_okb fildes 8)
      then
        /- [access_ok] refuses the range: -EFAULT with nothing installed.
           Mirrors [Fs.Pipe.pipe2_spec]'s guard of the same name; the
           argument is there. -/
        match eff with
        | ⟨ret, [], [], [], [], []⟩ =>
            if errno_ret_in (EFAULT :: pipe2_errnos) ret
            then .CheckOk m [] else .CheckReject
        | _ => .CheckReject
      else
      match read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
      | some _ =>
          match eff with
          | ⟨ret, [], [], [], [], []⟩ =>
              if errno_ret_in pipe2_errnos ret then .CheckOk m [] else .CheckReject
          | ⟨ret, [(a, bs)], [], [], [], []⟩ =>
              match fd_lookup (m_fds m) (pipe2_fdr m) with
              | some _ => .CheckReject   /- no free read-end fd: only the errno stands -/
              | none =>
                  match fd_lookup (pipe2_fds1 m id) (pipe2_fdw m id) with
                  | some _ => .CheckReject   /- no free write-end fd -/
                  | none =>
                      if bv_eqb ret (BitVec.ofInt 64 0) && bv_eqb a fildes
                         && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m)
                                            (pipe2_fdw m id))
                      then .CheckOk (pipe2_model m id) []
                      else .CheckReject
          | _ => .CheckReject
      | none =>
          match read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
          | none =>
              match eff with
              | ⟨ret, [], [], [], [], []⟩ =>
                  if errno_ret_in (EFAULT :: pipe2_errnos) ret
                  then .CheckOk m [] else .CheckReject
              | _ => .CheckReject
          | some _ => .CheckUnmodeled   /- partially writable destination -/

/- =========================================================================
   Soundness: every outcome the checker accepts is one the spec admits
   ========================================================================= -/

theorem check_pipe2_sound_ok (i : SyscallInput) (fildes flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pipe2 i fildes flags eff m = .CheckOk m' evs) :
    pipe2_spec fildes flags i m (.ok eff m' evs) := by
  generalize hP : (pipe2_spec fildes flags i m (.ok eff m' evs)) = Q at *
  unfold check_pipe2 at H
  dsimp only at H
  by_cases hbad : (!(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)) = true
  · -- a bit outside the accepted mask: -EINVAL, before anything else
    rw [ite_eq_left hbad] at H
    obtain ⟨heff, hm, hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    subst heff
    subst m'
    subst hevs
    rw [← hP]
    unfold pipe2_spec
    try dsimp only
    refine bind_ok0 inputSpec _ i m i m _ _ [] rfl ?_
    try dsimp only
    refine bind_ok0 getModelSpec _ i m m m _ _ [] rfl ?_
    try dsimp only
    simp only [ite_eq_left hbad, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right hbad] at H
    by_cases hnz : (!(w_is0 flags)) = true
    · -- an accepted but uninterpreted flag: the checker declines
      rw [ite_eq_left hnz] at H
      exact nomatch H
    · rw [ite_eq_right hnz] at H
      try dsimp only at H
      cases hid : pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
      | some st =>
        simp only [hid] at H
        exact nomatch H
      | none =>
        simp only [hid] at H
        by_cases hak : (!(access_okb fildes 8)) = true
        · -- [access_ok] refuses the range: -EFAULT, or one of the injected
          -- errnos alongside it, with nothing installed
          rw [ite_eq_left hak] at H
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws with
          | nil =>
            cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
            · by_cases he : errno_ret_in (EFAULT :: pipe2_errnos) ret = true
              · rw [ite_eq_left he] at H
                cases H
                obtain ⟨e, hmem, rfl⟩ :=
                  (errno_ret_in_true (EFAULT :: pipe2_errnos) ret).mp he
                rw [← hP]
                unfold pipe2_spec
                try dsimp only
                refine bind_ok0 inputSpec _ i m i m _ _ [] rfl ?_
                try dsimp only
                refine bind_ok0 getModelSpec _ i m m m _ _ [] rfl ?_
                try dsimp only
                simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_left hak]
                rcases List.mem_cons.mp hmem with rfl | hmem
                · refine alt_r _ _ i m _ ?_
                  simp only [err_ret, ret_only,
                    LinuxSem.LinuxProcessSem.pure]
                · refine alt_l _ _ i m _ ?_
                  refine bind_ok0 (errno_from pipe2_errnos) (fun er => err_ret er)
                    i m e m _ _ [] ?_ ?_
                  · exact choose_ok (fun x => x ∈ pipe2_errnos) e i m hmem
                  · simp only [err_ret, ret_only,
                      LinuxSem.LinuxProcessSem.pure]
              · rw [ite_eq_right he] at H
                exact nomatch H
            all_goals (exact nomatch H)
          | cons hd tl =>
            obtain ⟨a, bs⟩ := hd
            cases tl with
            | nil =>
              cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
              all_goals (exact nomatch H)
            | cons hd2 tl2 =>
              dsimp only at H
              exact nomatch H
        · rw [ite_eq_right hak] at H
          cases h8 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
          | some w8 =>
            simp only [h8] at H
            obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
            cases ws with
            | nil =>
              cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
              · -- the injected environment errno
                by_cases he : errno_ret_in pipe2_errnos ret = true
                · rw [ite_eq_left he] at H
                  cases H
                  obtain ⟨e, hmem, rfl⟩ :=
                    (errno_ret_in_true pipe2_errnos ret).mp he
                  rw [← hP]
                  unfold pipe2_spec
                  try dsimp only
                  refine bind_ok0 inputSpec _ i m i m _ _ [] rfl ?_
                  try dsimp only
                  refine bind_ok0 getModelSpec _ i m m m _ _ [] rfl ?_
                  try dsimp only
                  simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8]
                  refine alt_l _ _ i m _ ?_
                  refine bind_ok0 (errno_from pipe2_errnos) (fun er => err_ret er)
                    i m e m _ _ [] ?_ ?_
                  · exact choose_ok (fun x => x ∈ pipe2_errnos) e i m hmem
                  · simp only [err_ret, ret_only,
                      LinuxSem.LinuxProcessSem.pure]
                · rw [ite_eq_right he] at H
                  exact nomatch H
              all_goals (exact nomatch H)
            | cons hd tl =>
              obtain ⟨a, bs⟩ := hd
              cases tl with
              | nil =>
                cases zs <;> cases us <;> cases cs <;> cases ks <;>
                  dsimp only at H
                · -- the copy-out of two fresh descriptors
                  cases hfr : fd_lookup (m_fds m) (pipe2_fdr m) with
                  | some x =>
                    simp only [hfr] at H
                    exact nomatch H
                  | none =>
                    simp only [hfr] at H
                    cases hfw : fd_lookup (pipe2_fds1 m (pipe_new_id (m_pipes m)))
                        (pipe2_fdw m (pipe_new_id (m_pipes m))) with
                    | some y =>
                      simp only [hfw] at H
                      exact nomatch H
                    | none =>
                      simp only [hfw] at H
                      by_cases hg : (bv_eqb ret (BitVec.ofInt 64 0) && bv_eqb a fildes
                          && listN_eqb bs (pipe_fd_bytes (pipe2_fdr m)
                              (pipe2_fdw m (pipe_new_id (m_pipes m))))) = true
                      · rw [ite_eq_left hg] at H
                        cases H
                        have h12 : (bv_eqb ret (BitVec.ofInt 64 0) && bv_eqb a fildes)
                            = true := (Bool.and_eq_true ..).mp hg |>.1
                        have hbs0 : listN_eqb bs (pipe_fd_bytes (pipe2_fdr m)
                              (pipe2_fdw m (pipe_new_id (m_pipes m)))) = true :=
                          (Bool.and_eq_true ..).mp hg |>.2
                        have hret : ret = BitVec.ofInt 64 0 :=
                          (Fs.bv_eqb_eq _ _).mp ((Bool.and_eq_true ..).mp h12).1
                        have ha : a = fildes :=
                          (Fs.bv_eqb_eq _ _).mp ((Bool.and_eq_true ..).mp h12).2
                        have hbs : bs = pipe_fd_bytes (pipe2_fdr m)
                            (pipe2_fdw m (pipe_new_id (m_pipes m))) :=
                          (listN_eqb_eq _ _).mp hbs0
                        subst hret
                        subst ha
                        subst hbs
                        rw [← hP]
                        unfold pipe2_spec
                        try dsimp only
                        refine bind_ok0 inputSpec _ i m i m _ _ [] rfl ?_
                        try dsimp only
                        refine bind_ok0 getModelSpec _ i m m m _ _ [] rfl ?_
                        try dsimp only
                        simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8]
                        refine alt_r _ _ i m _ ?_
                        refine bind_ok0 (lowest_fd (m_fds m)) _ i m (pipe2_fdr m) m
                          _ _ [] ?_ ?_
                        · refine choose_ok _ _ i m ⟨?_, rfl⟩
                          exact hfr
                        · try dsimp only
                          refine bind_ok0
                            (lowest_fd (pipe2_fds1 m (pipe_new_id (m_pipes m))))
                            _ i m (pipe2_fdw m (pipe_new_id (m_pipes m))) m _ _ [] ?_ ?_
                          · refine choose_ok _ _ i m ⟨?_, rfl⟩
                            exact hfw
                          · try dsimp only
                            refine bind_ok0
                              (modifySpec (with_fds (fd_insert
                                (pipe2_fds1 m (pipe_new_id (m_pipes m)))
                                (pipe2_fdw m (pipe_new_id (m_pipes m)))
                                (FdEntry.FdPipe (pipe_new_id (m_pipes m)) true))))
                              _ i _ () _ _ _ [] rfl ?_
                            try dsimp only
                            refine bind_ok0
                              (modifySpec (with_pipes (pipe_insert (m_pipes m)
                                (pipe_new_id (m_pipes m)) (([], (0 : Int))))))
                              _ i _ () _ _ _ [] rfl ?_
                            try dsimp only
                            simp only [LinuxSem.LinuxProcessSem.pure]
                            rfl
                      · rw [ite_eq_right hg] at H
                        exact nomatch H
                all_goals (exact nomatch H)
              | cons hd2 tl2 =>
                dsimp only at H
                exact nomatch H
          | none =>
            simp only [h8] at H
            cases h1 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
            | some w1 =>
              simp only [h1] at H
              exact nomatch H
            | none =>
              simp only [h1] at H
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
                dsimp only at H
              · by_cases he : errno_ret_in (EFAULT :: pipe2_errnos) ret = true
                · rw [ite_eq_left he] at H
                  cases H
                  obtain ⟨e, hmem, rfl⟩ :=
                    (errno_ret_in_true (EFAULT :: pipe2_errnos) ret).mp he
                  rw [← hP]
                  unfold pipe2_spec
                  try dsimp only
                  refine bind_ok0 inputSpec _ i m i m _ _ [] rfl ?_
                  try dsimp only
                  refine bind_ok0 getModelSpec _ i m m m _ _ [] rfl ?_
                  try dsimp only
                  simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8, h1]
                  rcases List.mem_cons.mp hmem with rfl | hmem
                  · refine alt_r _ _ i m _ ?_
                    simp only [err_ret, ret_only,
                      LinuxSem.LinuxProcessSem.pure]
                  · refine alt_l _ _ i m _ ?_
                    refine bind_ok0 (errno_from pipe2_errnos) (fun er => err_ret er)
                      i m e m _ _ [] ?_ ?_
                    · exact choose_ok (fun x => x ∈ pipe2_errnos) e i m hmem
                    · simp only [err_ret, ret_only,
                        LinuxSem.LinuxProcessSem.pure]
                · rw [ite_eq_right he] at H
                  exact nomatch H
              all_goals (exact nomatch H)

theorem check_pipe2_sound_unmodeled (i : SyscallInput) (fildes flags : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_pipe2 i fildes flags eff m = .CheckUnmodeled) :
    pipe2_spec fildes flags i m .unmodeled := by
  generalize hP : (pipe2_spec fildes flags i m .unmodeled) = Q at *
  unfold check_pipe2 at H
  dsimp only at H
  by_cases hbad : (!(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)) = true
  · -- a bit outside the accepted mask: the checker answers -EINVAL here
    rw [ite_eq_left hbad] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hbad] at H
    by_cases hnz : (!(w_is0 flags)) = true
    · rw [ite_eq_left hnz] at H
      rw [← hP]
      unfold pipe2_spec
      try dsimp only
      refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
      try dsimp only
      refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
      try dsimp only
      simp only [ite_eq_right hbad, ite_eq_left hnz, unmodeled]
    · rw [ite_eq_right hnz] at H
      try dsimp only at H
      cases hid : pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
      | some st =>
        simp only [hid] at H
        rw [← hP]
        unfold pipe2_spec
        try dsimp only
        refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
        try dsimp only
        refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
        try dsimp only
        simp only [ite_eq_right hbad, ite_eq_right hnz, hid, unmodeled]
      | none =>
        simp only [hid] at H
        by_cases hak : (!(access_okb fildes 8)) = true
        · -- dead: this arm answers -EFAULT or an injected errno, never a
          -- decline
          rw [ite_eq_left hak] at H
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws with
          | nil =>
            cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
            · repeat (split at H)
              all_goals (exact nomatch H)
            all_goals (exact nomatch H)
          | cons hd tl =>
            obtain ⟨a, bs⟩ := hd
            cases tl with
            | nil =>
              cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
              all_goals (exact nomatch H)
            | cons hd2 tl2 =>
              dsimp only at H
              exact nomatch H
        · rw [ite_eq_right hak] at H
          cases h8 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
          | some w8 =>
            simp only [h8] at H
            obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
            cases ws with
            | nil =>
              cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
              · repeat (split at H)
                all_goals (exact nomatch H)
              all_goals (exact nomatch H)
            | cons hd tl =>
              obtain ⟨a, bs⟩ := hd
              cases tl with
              | nil =>
                cases zs <;> cases us <;> cases cs <;> cases ks <;>
                  dsimp only at H
                · -- the copy-out arm: a free read end and a free write end
                  -- are what it tests, and either answer is accepted or
                  -- rejected, never declined
                  cases hfr : fd_lookup (m_fds m) (pipe2_fdr m) with
                  | some x =>
                    simp only [hfr] at H
                    exact nomatch H
                  | none =>
                    simp only [hfr] at H
                    cases hfw : fd_lookup (pipe2_fds1 m (pipe_new_id (m_pipes m)))
                        (pipe2_fdw m (pipe_new_id (m_pipes m))) with
                    | some y =>
                      simp only [hfw] at H
                      exact nomatch H
                    | none =>
                      simp only [hfw] at H
                      repeat (split at H)
                      all_goals (exact nomatch H)
                all_goals (exact nomatch H)
              | cons hd2 tl2 =>
                dsimp only at H
                exact nomatch H
          | none =>
            simp only [h8] at H
            cases h1 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
            | some w1 =>
              -- a writable prefix and an unwritable tail: the one arm the
              -- checker declines
              simp only [h1] at H
              rw [← hP]
              unfold pipe2_spec
              try dsimp only
              refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
              try dsimp only
              refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
              try dsimp only
              simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8, h1, unmodeled]
            | none =>
              simp only [h1] at H
              obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
              cases ws with
              | nil =>
                cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
                · repeat (split at H)
                  all_goals (exact nomatch H)
                all_goals (exact nomatch H)
              | cons hd tl =>
                obtain ⟨a, bs⟩ := hd
                cases tl with
                | nil =>
                  cases zs <;> cases us <;> cases cs <;> cases ks <;>
                    dsimp only at H
                  all_goals (exact nomatch H)
                | cons hd2 tl2 =>
                  dsimp only at H
                  exact nomatch H

/- =========================================================================
   Private inversion helpers
   =========================================================================

   The completeness proofs below need the spec hypothesis broken into
   branch facts — the job of an `inv_ok`-style `repeat first [...]` loop
   over the `bind`/`choose`/`alt`/`modify`/`pure` bodies.  Lean has no
   `match goal`, and `inv_ok` (`Checks.Sys.Prelude`) deliberately stops at
   constructor injectivities, so the same facts are stated here once each
   and cited below.  Every statement is the *definitional* reading of one
   combinator, so the lemmas are one `simp only` apiece.

   (`bind_inputSpec` is the prologue peel: `i <- input ;; m <- get_model`
   reads the input and the model it started in, so the body is stated at
   `i` and `m`.  It is `Checks.Witness.Kernel.Sched.Syscalls`' lemma of the
   same name, restated here because that one is `private`.) -/

private theorem bind_inputSpec {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event) :
    bind inputSpec k i m o ↔ k i i m o := by
  cases o with
  | ok x m' evs =>
      simp only [LinuxSem.LinuxProcessSem.bind]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        simp only [inputSpec, input, Outcome.ok.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        simp only [List.nil_append] at h3
        subst h3
        exact h2
      · intro h
        exact ⟨i, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
      simp only [LinuxSem.LinuxProcessSem.bind]
      constructor
      · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
        · exact absurd h (by simp [inputSpec, input])
        · simp only [inputSpec, input, Outcome.ok.injEq] at h1
          obtain ⟨rfl, rfl, rfl⟩ := h1
          exact h2
      · intro h
        exact Or.inr ⟨i, m, [], rfl, h⟩

theorem modifySpec_ok_inv (f : Model → Model) (i : SyscallInput) (m : Model) (u : Unit)
    (m' : Model) (evs : List event) (H : modifySpec f i m (.ok u m' evs)) :
    m' = f m ∧ evs = [] := by
  simp only [modifySpec, LinuxSem.LinuxProcessSem.modify,
    Outcome.ok.injEq] at H
  exact ⟨H.2.1, H.2.2⟩

theorem modifySpec_not_unmodeled (f : Model → Model) (i : SyscallInput) (m : Model) :
    ¬ modifySpec f i m .unmodeled := by
  intro H
  simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at H
  exact nomatch H

theorem pure_not_unmodeled {A : Type} (x : A) (i : SyscallInput) (m : Model) :
    ¬ LinuxSem.LinuxProcessSem.pure (M := Model) (I := SyscallInput)
        (E := event) x i m .unmodeled := by
  intro H
  simp only [LinuxSem.LinuxProcessSem.pure] at H
  exact nomatch H

theorem lowest_fd_ok_inv (fds : List (word × FdEntry)) (i : SyscallInput) (m : Model)
    (fd : word) (m' : Model) (evs : List event)
    (H : lowest_fd fds i m (.ok fd m' evs)) :
    fd_lookup fds fd = none ∧ fd = alloc_fd fds ∧ m' = m ∧ evs = [] := by
  obtain ⟨x, ⟨hfree, hx⟩, heq⟩ := H
  simp only [Outcome.ok.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨hfree, hx, rfl, rfl⟩

theorem lowest_fd_not_unmodeled (fds : List (word × FdEntry)) (i : SyscallInput)
    (m : Model) : ¬ lowest_fd fds i m .unmodeled := by
  intro H
  obtain ⟨x, -, heq⟩ := H
  exact nomatch heq

theorem err_ret_ok_inv (e : Int) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (H : err_ret e i m (.ok eff m' evs)) :
    eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
    Outcome.ok.injEq] at H
  exact H

theorem err_ret_not_unmodeled (e : Int) (i : SyscallInput) (m : Model) :
    ¬ err_ret e i m .unmodeled := by
  intro H
  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
  exact nomatch H

theorem errno_from_err_ret_ok_inv (es : List Int) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : bind (errno_from es) (fun e => err_ret e) i m (.ok eff m' evs)) :
    ∃ e, e ∈ es ∧ eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  obtain ⟨x, m1, evs1, evs2, hc, he, hevs⟩ := H
  obtain ⟨e, hmem, heq⟩ := hc
  cases heq
  obtain ⟨heff, hm, hevs2⟩ := err_ret_ok_inv x i m eff m' evs2 he
  refine ⟨x, hmem, heff, ?_⟩
  rw [hm, hevs, hevs2]
  simp

theorem errno_from_err_ret_not_unmodeled (es : List Int) (i : SyscallInput)
    (m : Model) : ¬ bind (errno_from es) (fun e => err_ret e) i m .unmodeled := by
  intro H
  unfold LinuxSem.LinuxProcessSem.bind at H
  dsimp only at H
  cases H with
  | inl H1 =>
    obtain ⟨e, _hmem, heq⟩ := H1
    exact nomatch heq
  | inr H2 =>
    obtain ⟨x, m1, evs1, hc, he⟩ := H2
    exact absurd he (err_ret_not_unmodeled x i m1)

/-- One `bind`'s unmodeled case, as a rewrite rule (the definition is a
    `match` on the outcome, which `rw` cannot see through). -/
theorem bind_unmodeled_iff {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) :
    bind c k i m .unmodeled ↔
      c i m .unmodeled ∨ ∃ x m1 evs1, c i m (.ok x m1 evs1) ∧ k x i m1 .unmodeled :=
  Iff.rfl

/-- The copy-out chain of `pipe2_spec` — two `lowest_fd` allocations, the
    fd install, the pipe install and the returned effect — named so the two
    lemmas below can talk about it without restating it.  It is the
    spec's own [alt] branch read as a definition (the spec keeps it inline
    because that is where its prose lives). -/
def pipe2_chain (fds : List (word × FdEntry)) (ps : List (word × PipeBuf))
    (fildes : word) (id : word) : SysSpec SyscallEffect :=
  bind (lowest_fd fds) (fun fdr =>
    bind (lowest_fd (fd_insert fds fdr (FdEntry.FdPipe id false))) (fun fdw =>
      bind (modifySpec (with_fds (fd_insert
          (fd_insert fds fdr (FdEntry.FdPipe id false)) fdw
          (FdEntry.FdPipe id true)))) (fun _ =>
        bind (modifySpec (with_pipes (pipe_insert ps id ([], (0 : Int))))) (fun _ =>
          LinuxSem.LinuxProcessSem.pure
            (mkEffect (BitVec.ofInt 64 0) [(fildes, pipe_fd_bytes fdr fdw)] [])))))

/-- …read back as the facts the checker tests: both descriptors free, the
    one eight-byte write, the model `pipe2_model` builds, and no events.
    Reading the chain back gives exactly these, one `dsimp only` apiece. -/
theorem pipe2_chain_ok_inv (fds : List (word × FdEntry)) (ps : List (word × PipeBuf))
    (fildes : word) (id : word) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : pipe2_chain fds ps fildes id i m (.ok eff m' evs)) :
    ∃ fdr fdw, fdr = alloc_fd fds ∧ fd_lookup fds fdr = none ∧
      fdw = alloc_fd (fd_insert fds fdr (FdEntry.FdPipe id false)) ∧
      fd_lookup (fd_insert fds fdr (FdEntry.FdPipe id false)) fdw = none ∧
      eff = mkEffect (BitVec.ofInt 64 0) [(fildes, pipe_fd_bytes fdr fdw)] [] ∧
      m' = with_pipes (pipe_insert ps id ([], (0 : Int)))
        (with_fds (fd_insert (fd_insert fds fdr (FdEntry.FdPipe id false)) fdw
          (FdEntry.FdPipe id true)) m) ∧
      evs = [] := by
  unfold pipe2_chain at H
  obtain ⟨fdr, m1, evs1, evs2, hlow, hrest, hevs⟩ := H
  obtain ⟨hfdr, hfdr_eq, hm1, hevs1⟩ := lowest_fd_ok_inv fds i m fdr m1 evs1 hlow
  subst m1
  subst hevs1
  simp only [List.nil_append] at hevs
  try dsimp only at hrest
  obtain ⟨fdw, m2, evs3, evs4, hlow2, hrest2, hevs4⟩ := hrest
  obtain ⟨hfdw, hfdw_eq, hm2, hevs3⟩ := lowest_fd_ok_inv _ i m fdw m2 evs3 hlow2
  subst m2
  subst hevs3
  simp only [List.nil_append] at hevs4
  obtain ⟨u, m3, evs5, evs6, hmod, hrest3, hevs6⟩ := hrest2
  obtain ⟨hm3, hevs5⟩ := modifySpec_ok_inv _ i m u m3 evs5 hmod
  subst m3
  subst hevs5
  simp only [List.nil_append] at hevs6
  obtain ⟨u2, m4, evs7, evs8, hmod2, hpure, hevs8⟩ := hrest3
  obtain ⟨hm4, hevs7⟩ := modifySpec_ok_inv _ i _ u2 m4 evs7 hmod2
  try simp only [List.nil_append] at hevs7
  try simp only [List.nil_append] at hevs8
  simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hpure
  obtain ⟨heff, hm', hevs'⟩ := hpure
  refine ⟨fdr, fdw, hfdr_eq, hfdr, hfdw_eq, hfdw, heff, ?_, ?_⟩
  · subst m'
    subst m4
    rfl
  · rw [hevs, hevs4, hevs6, hevs8, hevs']
    simp [hevs7]

/-- …and the same chain is never `unmodeled`: every step either allocates,
    writes the model, or returns, and none of those declines. -/
theorem pipe2_chain_unmodeled_false (fds : List (word × FdEntry))
    (ps : List (word × PipeBuf)) (fildes : word) (id : word) (i : SyscallInput)
    (m : Model) :
    ¬ pipe2_chain fds ps fildes id i m .unmodeled := by
  intro H
  unfold pipe2_chain at H
  rw [bind_unmodeled_iff] at H
  cases H with
  | inl H1 => exact lowest_fd_not_unmodeled fds i m H1
  | inr H2 =>
    obtain ⟨fdr, m1, evs1, hlow, hrest⟩ := H2
    try dsimp only at hrest
    rw [bind_unmodeled_iff] at hrest
    cases hrest with
    | inl H3 =>
      exact lowest_fd_not_unmodeled (fd_insert fds fdr (FdEntry.FdPipe id false)) i m1 H3
    | inr H4 =>
      obtain ⟨fdw, m2, evs2, hlow2, hrest2⟩ := H4
      try dsimp only at hrest2
      rw [bind_unmodeled_iff] at hrest2
      cases hrest2 with
      | inl H5 => exact modifySpec_not_unmodeled _ i m2 H5
      | inr H6 =>
        obtain ⟨u, m3, evs3, hmod, hrest3⟩ := H6
        try dsimp only at hrest3
        rw [bind_unmodeled_iff] at hrest3
        cases hrest3 with
        | inl H7 => exact modifySpec_not_unmodeled _ i m3 H7
        | inr H8 =>
          obtain ⟨u2, m4, evs4, hmod2, hpure⟩ := H8
          exact pure_not_unmodeled _ i m4 hpure

/- =========================================================================
   Completeness: every outcome the spec admits is one the checker accepts
   ========================================================================= -/

theorem check_pipe2_complete_ok (i : SyscallInput) (fildes flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : pipe2_spec fildes flags i m (.ok eff m' evs)) :
    check_pipe2 i fildes flags eff m = .CheckOk m' evs := by
  generalize hP : (check_pipe2 i fildes flags eff m = .CheckOk m' evs) = Q at *
  unfold pipe2_spec at H
  simp only [bind_inputSpec, getModelSpec, bind_getModel] at H
  by_cases hbad : (!(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)) = true
  · -- -EINVAL
    simp only [ite_eq_left hbad] at H
    obtain ⟨heff, hm, hevs⟩ := err_ret_ok_inv EINVAL i m eff m' evs H
    subst heff
    subst m'
    subst hevs
    rw [← hP]
    unfold check_pipe2
    try dsimp only
    rw [ite_eq_left hbad]
    simp only [check_ret_only, Fs.bv_eqb_eq]
    rfl
  · simp only [ite_eq_right hbad] at H
    by_cases hnz : (!(w_is0 flags)) = true
    · -- an accepted but uninterpreted flag
      simp only [ite_eq_left hnz, unmodeled] at H
      exact nomatch H
    · simp only [ite_eq_right hnz] at H
      cases hid : pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
      | some st =>
        simp only [hid, unmodeled] at H
        exact nomatch H
      | none =>
        simp only [hid] at H
        by_cases hak : (!(access_okb fildes 8)) = true
        · -- the injected errno, or -EFAULT, with nothing installed
          simp only [ite_eq_left hak] at H
          rw [← hP]
          unfold check_pipe2
          try dsimp only
          simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_left hak]
          cases H with
          | inl Hinj =>
            obtain ⟨e, hmem, heff, hm, hevs⟩ := errno_from_err_ret_ok_inv _ _ _ _ _ _ Hinj
            subst heff
            subst m'
            subst hevs
            try dsimp only
            rw [ite_eq_left (errno_ret_in_intro (EFAULT :: pipe2_errnos) e (by simp [hmem]))]
          | inr Hfault =>
            obtain ⟨heff, hm, hevs⟩ := err_ret_ok_inv EFAULT i m eff m' evs Hfault
            subst heff
            subst m'
            subst hevs
            try dsimp only
            rw [ite_eq_left (errno_ret_in_intro (EFAULT :: pipe2_errnos) EFAULT (by simp))]
        · simp only [ite_eq_right hak] at H
          cases h8 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
          | some w8 =>
            simp only [h8] at H
            rw [← hP]
            unfold check_pipe2
            try dsimp only
            simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8]
            cases H with
            | inl Hinj =>
              obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                errno_from_err_ret_ok_inv _ _ _ _ _ _ Hinj
              subst heff
              subst m'
              subst hevs
              try dsimp only
              rw [ite_eq_left (errno_ret_in_intro pipe2_errnos e hmem)]
            | inr Hsucc =>
              obtain ⟨fdr, fdw, hfdr_eq, hfdr, hfdw_eq, hfdw, heff, hm, hevs⟩ :=
                pipe2_chain_ok_inv (m_fds m) (m_pipes m) fildes
                  (pipe_new_id (m_pipes m)) i m eff m' evs Hsucc
              subst fdr
              subst fdw
              subst heff
              subst m'
              subst hevs
              try dsimp only
              rw [ite_eq_left (by
                simp [bv_eqb_refl, listN_eqb_eq, pipe2_fdr, pipe2_fds1, pipe2_fdw])]
              simp only [pipe2_fdr, pipe2_fds1, pipe2_fdw, pipe2_model, hfdr, hfdw]
              try rfl
          | none =>
            simp only [h8] at H
            cases h1 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
            | some w1 =>
              simp only [h1, unmodeled] at H
              exact nomatch H
            | none =>
              simp only [h1] at H
              rw [← hP]
              unfold check_pipe2
              try dsimp only
              simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8, h1]
              cases H with
              | inl Hinj =>
                obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                  errno_from_err_ret_ok_inv _ _ _ _ _ _ Hinj
                subst heff
                subst m'
                subst hevs
                try dsimp only
                rw [ite_eq_left (errno_ret_in_intro (EFAULT :: pipe2_errnos) e (by simp [hmem]))]
              | inr Hfault =>
                obtain ⟨heff, hm, hevs⟩ := err_ret_ok_inv EFAULT i m eff m' evs Hfault
                subst heff
                subst m'
                subst hevs
                try dsimp only
                rw [ite_eq_left (errno_ret_in_intro (EFAULT :: pipe2_errnos) EFAULT (by simp))]

theorem check_pipe2_complete_unmodeled (i : SyscallInput) (fildes flags : word)
    (m : Model) (eff : SyscallEffect)
    (H : pipe2_spec fildes flags i m .unmodeled) :
    check_pipe2 i fildes flags eff m = .CheckUnmodeled := by
  generalize hP : (check_pipe2 i fildes flags eff m = .CheckUnmodeled) = Q at *
  unfold pipe2_spec at H
  simp only [bind_inputSpec, getModelSpec, bind_getModel] at H
  by_cases hbad : (!(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0)) = true
  · simp only [ite_eq_left hbad, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · simp only [ite_eq_right hbad] at H
    by_cases hnz : (!(w_is0 flags)) = true
    · simp only [ite_eq_left hnz, unmodeled] at H
      rw [← hP]
      unfold check_pipe2
      try dsimp only
      simp only [ite_eq_right hbad, ite_eq_left hnz]
    · simp only [ite_eq_right hnz] at H
      cases hid : pipe_lookup (m_pipes m) (pipe_new_id (m_pipes m)) with
      | some st =>
        simp only [hid, unmodeled] at H
        rw [← hP]
        unfold check_pipe2
        try dsimp only
        simp only [ite_eq_right hbad, ite_eq_right hnz, hid]
      | none =>
        simp only [hid] at H
        by_cases hak : (!(access_okb fildes 8)) = true
        · simp only [ite_eq_left hak] at H
          cases H with
          | inl H1 => exact absurd H1 (errno_from_err_ret_not_unmodeled _ _ _)
          | inr H2 => exact absurd H2 (err_ret_not_unmodeled EFAULT i m)
        · simp only [ite_eq_right hak] at H
          cases h8 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
          | some w8 =>
            simp only [h8] at H
            cases H with
            | inl H1 => exact absurd H1 (errno_from_err_ret_not_unmodeled _ _ _)
            | inr H2 =>
              exact absurd H2
                (pipe2_chain_unmodeled_false (m_fds m) (m_pipes m) fildes
                  (pipe_new_id (m_pipes m)) i m)
          | none =>
            simp only [h8] at H
            cases h1 : read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
            | some w1 =>
              simp only [h1, unmodeled] at H
              rw [← hP]
              unfold check_pipe2
              try dsimp only
              simp only [ite_eq_right hbad, ite_eq_right hnz, hid, ite_eq_right hak, h8, h1]
            | none =>
              simp only [h1] at H
              cases H with
              | inl H1 => exact absurd H1 (errno_from_err_ret_not_unmodeled _ _ _)
              | inr H2 => exact absurd H2 (err_ret_not_unmodeled EFAULT i m)

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal.  These pin the branch
   order the four proofs above follow, one per claim the spec's prose
   makes: a bit outside the mask is -EINVAL before anything else, an
   accepted-but-uninterpreted flag declines, an unwritable destination is
   -EFAULT with the model untouched, a partially writable one declines,
   and the copy-out of two fresh descriptors is accepted at
   `pipe2_model`.

   `check_result` carries no `DecidableEq` (a `CheckOk` carries a `Model`,
   whose fd table reaches the coinductive `SockState`), so each states the
   branch as an equation and closes it by unfolding the checker and
   discharging the tests with `decide`. -/

/-- Every destination is writable, every byte zero. -/
private def portWmem : word → Option byte := fun _ => some 0

/-- The model the checks run in: an empty fd table, an empty pipe table, an
    empty VM ledger, EOF on stdin and no halt. -/
private def portModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A `pipe2` input: `fildes = 0x1000`, `flags = 0`. -/
private def portInput : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := portWmem }

/-- The read end on an empty fd table is descriptor 0. -/
example : pipe2_fdr portModel = 0 := by decide

/-- …and the write end is 1: the scan starts above the reserved read end. -/
example : pipe2_fdw portModel 0 = 1 := by decide

/-- `pipe2_flags_mask` is the four accepted bits, and `pipe2_errnos` is the
    three injectable failures (the `Sys` module's own checks pin both; they
    are restated here so this file's proofs can be read beside them). -/
example : pipe2_flags_mask = 542848 := by decide

example : pipe2_errnos = [24, 23, 12] := by decide

/-- A bit outside the accepted mask is -EINVAL, and the acceptor is exactly
    the return-only one — nothing else about the call is looked at. -/
example (eff : SyscallEffect) :
    check_pipe2 portInput 0x1000 1 eff portModel
      = check_ret_only eff (errno_ret EINVAL) portModel [] := by
  have hbad : (!(z_ldiff ((1 : word).toNat : Int) pipe2_flags_mask == 0)) = true := by
    decide
  simp only [check_pipe2]
  rw [ite_eq_left hbad]

/-- An accepted but uninterpreted flag (`O_CLOEXEC`) declines: the model
    interprets only the ABSENCE of all four. -/
example (eff : SyscallEffect) :
    check_pipe2 portInput 0x1000 0x80000 eff portModel = .CheckUnmodeled := by
  have hbad : (!(z_ldiff ((0x80000 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hnz : (!(w_is0 (0x80000 : word))) = true := by decide
  simp only [check_pipe2]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_left hnz]

/-- A destination `access_ok` refuses is -EFAULT with nothing installed —
    the model unchanged, as `do_pipe2`'s `fput` and `put_unused_fd` unwind
    both ends. -/
example :
    check_pipe2 portInput (BitVec.allOnes 64) 0
        (mkEffect (errno_ret EFAULT) [] []) portModel
      = .CheckOk portModel [] := by
  have hbad : (!(z_ldiff ((0 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hz : (!(w_is0 (0 : word))) = false := by decide
  have hak : (!(access_okb (BitVec.allOnes 64) 8)) = true := by decide
  have he : errno_ret_in (EFAULT :: pipe2_errnos) (errno_ret EFAULT) = true := by
    decide
  simp only [check_pipe2, portInput, portModel, mkModel, m_pipes,
    pipe_new_id, pipe_lookup]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_right (by rw [hz]; simp), ite_eq_left hak, ite_eq_left he]

/-- A writable view with exactly ONE byte mapped at the destination. -/
private def oneByteWmem : word → Option byte :=
  fun a => if a == (0x1000 : word) then some 0 else none

/-- A `pipe2` input whose destination is writable for one byte only. -/
private def portInputPartial : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := oneByteWmem }

/-- …so the eight-byte walk does not fit but the one-byte probe does. -/
example : read_bytes_map oneByteWmem (0x1000 : word) (BitVec.ofInt 64 8) = none := by
  decide

example : read_bytes_map oneByteWmem (0x1000 : word) (BitVec.ofInt 64 1) = some [0] := by
  decide

/-- A partially writable destination declines: `copy_to_user` leaves an
    architecture-dependent number of bytes behind. -/
example (eff : SyscallEffect) :
    check_pipe2 portInputPartial 0x1000 0 eff portModel = .CheckUnmodeled := by
  have hbad : (!(z_ldiff ((0 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hz : (!(w_is0 (0 : word))) = false := by decide
  have hak : (!(access_okb (0x1000 : word) 8)) = false := by decide
  have h8 : read_bytes_map oneByteWmem (0x1000 : word) (BitVec.ofInt 64 8) = none := by
    decide
  have h1 : read_bytes_map oneByteWmem (0x1000 : word) (BitVec.ofInt 64 1) = some [0] := by
    decide
  simp only [check_pipe2, portInputPartial, portModel, mkModel, m_pipes, pipe_new_id,
    pipe_lookup]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_right (by rw [hz]; simp), ite_eq_right (by rw [hak]; simp),
    h8, h1]

/-- The success arm: the two fresh descriptors, the pipe installed empty,
    and the effect one eight-byte write of `int fildes[2]`. -/
example :
    check_pipe2 portInput 0x1000 0
        (mkEffect (BitVec.ofInt 64 0)
          [((0x1000 : word), pipe_fd_bytes (pipe2_fdr portModel)
              (pipe2_fdw portModel (pipe_new_id (m_pipes portModel))))] [])
        portModel
      = .CheckOk (pipe2_model portModel (pipe_new_id (m_pipes portModel))) [] := by
  have hbad : (!(z_ldiff ((0 : word).toNat : Int) pipe2_flags_mask == 0)) = false := by
    decide
  have hz : (!(w_is0 (0 : word))) = false := by decide
  have hak : (!(access_okb (0x1000 : word) 8)) = false := by decide
  have h8 : read_bytes_map portWmem (0x1000 : word) (BitVec.ofInt 64 8)
      = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hfr : fd_lookup (m_fds portModel) (pipe2_fdr portModel) = none := by decide
  have hfw : fd_lookup (pipe2_fds1 portModel (pipe_new_id (m_pipes portModel)))
      (pipe2_fdw portModel (pipe_new_id (m_pipes portModel))) = none := by decide
  simp only [check_pipe2]
  rw [ite_eq_right (by rw [hbad]; simp), ite_eq_right (by rw [hz]; simp), ite_eq_right (by rw [hak]; simp)]
  simp only [portInput, h8, hfr, hfw]
  simp only [portModel, mkModel, m_pipes, pipe_new_id, pipe_lookup]
  /- `exact ite_eq_left …`, not `rw [ite_eq_left …]`: on the closed `&&`
     chain over `listN_eqb` that is the last guard, `rw` reports "did not
     find an occurrence of the pattern" for the very `if` it is looking
     at, while `exact` unifies the same equation against the goal. -/
  exact ite_eq_left (by decide)

end LinuxSem.Checks.Sys.Fs.Pipe
