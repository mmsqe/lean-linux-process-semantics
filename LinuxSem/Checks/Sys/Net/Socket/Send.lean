/-
  * LinuxProcessSem.Checks.Sys.Net.Socket.Send — the `send` family's
    (206 `sendto`, 211 `sendmsg`) checker soundness and completeness

  The two agreement quadruples for the `send` family — `sendto` (206) and
  `sendmsg` (211) — split out of the parent module so that it stops growing
  as each send arm lands.  The statements are the parent's
  `check_send_on_socket` / `check_sendto` / `check_sendmsg` and
  `Sys/Net/Socket`'s `send_on_socket` / `sendto_spec` / `sendmsg_spec`
  verbatim; the helpers added here are marked in the sections below.

  WHY EVERY LEMMA IS SPLIT INTO PER-ARM LEMMAS.  A proof term that carries
  the UNFOLDED body of `check_sendmsg` through a case split is rejected by
  the kernel with "(kernel) deep recursion detected", and `maxRecDepth` does
  not lift it: the elaborated term of `check_sendmsg` contains the
  six-`read_u64` tree, `copy_iovecs_aux`'s fuel recursion and
  `send_on_socket`'s own match, and every `cases` that abstracts a variable
  inside it re-elaborates a term whose size is the product of the two arms.
  A proof confined to ONE ARM compiles.  So each public lemma here is a
  DISPATCH: it splits only on cheap scrutinees (`send_state sk`, the three
  model gates, `fd_lookup`, the header reads) and calls a per-arm lemma, and
  the per-arm lemma does its own `unfold check_send_* at H`, puts the spec
  side in the same shape with `unfold send*_spec` (or
  `unfold send_bytes at H` in the completeness direction), and closes with
  the leaf's builder or inverter.

  THE THREE WALKS, IN ORDER.  `send_on_socket` first: it is the building
  block the other two delegate their socket arm to, so the two
  `check_send_to` dispatches below only ever hand it an `H` that is still
  the folded checker application.  Then `sendto`, whose walk is the three
  gates, then `import_ubuf`'s range verdict, then the fd INSIDE it; then
  `sendmsg`, whose arm set is the six-`read_u64` tree: 63 of the 64 shapes
  are the total-match -EFAULT arm both sides agree on, and only the
  all-`some` one carries the call.

  TACTICS.  `simp only [] at H ⊢` — never `dsimp only at H ⊢` — is what
  reduces a `match` once its scrutinee has been rewritten: it is
  beta/iota/zeta with no rewrite rules, and unlike `dsimp` it does not
  re-elaborate the dependent motive.  A `match` on a variable is peeled with
  `by_cases h : <guard> = true`, `simp only [h, ite_true]` /
  `[h, Bool.false_eq_true, ite_false]`, and an effect's shape with
  `obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff` followed by
  `cases ws <;> cases zs <;> cases us <;> cases cs`: the fifteen shapes
  that are not all-empty are the checker's `_ => .CheckReject`, closed by
  `simp only [] at H; exact nomatch H`.  Constructor arguments that a
  `cases` determines (`ret`, `copyins` there) are NOT named.
-/
import LinuxSem.Checks.Sys.Net.Socket

namespace LinuxSem.Checks.Sys.Net.Socket

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
  (rw_bytes_max modeled_rw_count access_ok_zero)
open LinuxSem.LinuxProcessSem.Sys.Fs.File (lowest_fd)
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite (UIO_FASTIOV)
open LinuxSem.LinuxProcessSem.Sys.Net.Socket
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Uaccess (check_access_ok_zero)

/-! ### The leaves the send arms end in

  Four shapes, and each needs its builder (for the sound direction) and,
  for `choose`/`emit`, its inverter (for the completeness direction):
  `record_copyins reads (ret_only r)` for the zero-length and -EFAULT
  arms, `seqSpec (set_fds …) (ret_only r)` for the consumed pending
  error, and `seqSpec (emit …) (record_copyins … (ret_only …))` for the
  delivered prefix.  The parent file keeps its own copies of the first
  two under `private`, so they are restated here rather than imported. -/

/-- `record_copyins reads (ret_only r)` at its own accepted
    outcome: the ledger round the fixed return, at the same model. -/
private theorem send_record_copyins_ret_only_ok (reads : List (word × Nat)) (r : word)
    (i : SyscallInput) (m : Model) :
    record_copyins reads (ret_only r) i m
      (.ok (with_copyins reads (mkEffect r [] [])) m []) :=
  record_copyins_ok_empty rfl (ret_only_ok r i m)

/-- Invert that leaf.  The `-EPIPE`, `-EFAULT` and zero-length
    arms' spec stage covers exactly one outcome, so an accepted one names
    the effect, the model and the (empty) events. -/
private theorem send_record_copyins_ret_only_ok_inv (reads : List (word × Nat)) (r : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : record_copyins reads (ret_only r) i m (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] []) ∧ m' = m ∧ evs = [] := by
  obtain ⟨core, hcore, heff⟩ := record_copyins_ok_inv reads (ret_only r) i m eff m' evs H
  simp only [ret_only, LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hcore
  obtain ⟨rfl, rfl, rfl⟩ := hcore
  simp only [mkEffect, List.append_nil] at heff
  exact ⟨heff, rfl, rfl⟩

/-- `set_fds then ret_only` — the `SendErr` arm's spec stage,
    which consumes the pending error and installs `SkReset` before
    answering -`e`. -/
private theorem send_seqSpec_set_fds_ret_only_ok (fds : List (word × FdEntry)) (r : word)
    (i : SyscallInput) (m : Model) :
    seqSpec (set_fds fds) (ret_only r) i m
      (.ok (mkEffect r [] []) (with_fds fds m) []) := by
  refine ⟨(), with_fds fds m, [], [], ?_, ?_, by simp⟩
  · unfold set_fds modifySpec LinuxSem.LinuxProcessSem.modify
    rfl
  · exact ret_only_ok r i _

/-- The delivered-prefix leaf, at its own accepted outcome:
    the emitted trace is the delivered bytes' events and the ledger is the
    one the caller accumulated round the delivered length. -/
private theorem send_seqSpec_emit_record_ret_only_ok (evs0 : List event)
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model) :
    seqSpec (emit evs0) (record_copyins reads (ret_only r)) i m
      (.ok (with_copyins reads (mkEffect r [] [])) m evs0) := by
  refine ⟨(), m, evs0, [], rfl, ?_, by simp⟩
  exact record_copyins_ok_empty rfl (ret_only_ok r i _)

/-- Invert the delivered-prefix leaf: the emitted trace is the
    event list handed in, the model is untouched, and the effect is the
    ledger round the delivered length. -/
private theorem send_seqSpec_emit_record_ret_only_ok_inv (evs0 : List event)
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (emit evs0) (record_copyins reads (ret_only r)) i m
      (.ok eff m' evs)) :
    eff = with_copyins reads (mkEffect r [] []) ∧ m' = m ∧ evs = evs0 := by
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := H
  cases h1
  obtain ⟨heff, hm, hevs⟩ :=
    send_record_copyins_ret_only_ok_inv reads r i m eff m' ev2 h2
  rw [hevs, List.append_nil] at h3
  exact ⟨heff, hm, h3⟩

/-! ### The stages that cannot decline

  The completeness directions invert the spec's `.unmodeled`, and every
  leaf but the one the arm means to decline at is a stage that CANNOT
  decline.  `record_copyins`, `emit`, `choose` and `pure` are the four
  primitives involved; `bind`/`seqSpec` chains built out of them follow.
  The parent's `Fs.ReadWrite` module states the generic versions, but that
  module is outside this file's cone (and pulling it in to use four
  one-line facts would drag the whole write checker along), so the send
  leaves' shapes are restated here. -/

/-- `record_copyins reads (ret_only r)` never declines. -/
private theorem send_record_copyins_ret_only_no_unmodeled (reads : List (word × Nat))
    (r : word) (i : SyscallInput) (m : Model) :
    ¬ record_copyins reads (ret_only r) i m .unmodeled := by
  intro H
  have h := record_copyins_unmodeled_inv reads (ret_only r) i m H
  unfold ret_only LinuxSem.LinuxProcessSem.pure at h
  exact nomatch h

/-- `record_copyins reads (set_fds fds ;; ret_only r)` never
    declines — the `SendErr` arm's whole stage, ledger outside the setter. -/
private theorem send_record_copyins_set_fds_ret_only_no_unmodeled
    (fds : List (word × FdEntry)) (reads : List (word × Nat)) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ record_copyins reads (seqSpec (set_fds fds) (ret_only r)) i m .unmodeled := by
  intro H
  have H' := record_copyins_unmodeled_inv reads (seqSpec (set_fds fds) (ret_only r)) i m H
  simp only [seqSpec, LinuxSem.LinuxProcessSem.bind] at H'
  rcases H' with h | ⟨u, m1, evs1, h1, h2⟩
  · unfold set_fds modifySpec LinuxSem.LinuxProcessSem.modify at h
    exact nomatch h
  · cases h1
    unfold ret_only LinuxSem.LinuxProcessSem.pure at h2
    exact nomatch h2

/-- `emit then record_copyins (ret_only r)` never declines. -/
private theorem send_seqSpec_emit_record_ret_only_no_unmodeled (evs0 : List event)
    (reads : List (word × Nat)) (r : word) (i : SyscallInput) (m : Model) :
    ¬ seqSpec (emit evs0) (record_copyins reads (ret_only r)) i m .unmodeled := by
  intro H
  simp only [seqSpec, LinuxSem.LinuxProcessSem.bind] at H
  rcases H with h | ⟨u, m1, evs1, h1, h2⟩
  · simp only [emit] at h
    exact nomatch h
  · cases h1
    exact send_record_copyins_ret_only_no_unmodeled reads r i m h2

/-- The delivering arm's whole stage — `choose ;; emit ;;
    record_copyins ;; ret_only` — never declines, whatever the chosen
    prefix.  `choose` leaves the model alone, so the continuation runs at
    the model the arm started in. -/
private theorem send_choose_deliver_no_unmodeled (P : List byte → Prop)
    (f : List byte → List event) (reads : List byte → List (word × Nat))
    (r : List byte → word) (i : SyscallInput) (m : Model) :
    ¬ bind (choose P)
        (fun ds => seqSpec (emit (f ds))
          (record_copyins (reads ds) (ret_only (r ds)))) i m .unmodeled := by
  intro H
  simp only [LinuxSem.LinuxProcessSem.bind] at H
  rcases H with h | ⟨ds, m1, evs1, h1, h2⟩
  · obtain ⟨x, -, ho⟩ := h
    exact nomatch ho
  · obtain ⟨x, -, ho⟩ := h1
    cases ho
    exact send_seqSpec_emit_record_ret_only_no_unmodeled (f ds) (reads ds) (r ds) i m h2

/-- A prefix whose length a word bounds is far below `2^64`.
    The `choose` in `send_bytes` bounds `ds.length` by `total.toNat`, and
    `len_word_unsigned` needs that bound as an `Int` comparison. -/
private theorem send_length_lt_two_pow_64 {A : Type} (l : List A) (total : word)
    (h : (l.length : Int) ≤ (total.toNat : Int)) : (l.length : Int) < two_pow_64 := by
  have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
  have hlt : total.toNat < 2 ^ 64 := total.isLt
  omega

/- =========================================================================
   send_on_socket — the shared socket half, proved once
   ========================================================================= -/

/-! #### The three arms, accepted outcomes

  `send_state sk` is the only cheap scrutinee, so the dispatch below splits
  on it and each arm lemma takes the equation.  Inside an arm the spec's
  own split (`w_is0 total`, then `bs.length == 0`, then the effect's
  shape) is walked in the SAME `by_cases` as the checker's, which is what
  lets one hypothesis serve both sides. -/

/-- `SendDead` — -EPIPE, no model change. -/
private theorem send_sound_ok_dead (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (hst : send_state sk = SendState.SendDead)
    (H : check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs) :
    send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs) := by
  unfold check_send_on_socket at H
  simp only [hst] at H
  unfold send_on_socket
  simp only [hst]
  obtain ⟨heff, hm, hevs⟩ :=
    (check_ret_only_copyins_ok_iff pre eff (errno_ret EPIPE) m [] m' evs).mp H
  rw [heff, hm, hevs]
  exact send_record_copyins_ret_only_ok pre (errno_ret EPIPE) i m

/-- `SendErr e peer ch` — the pending error, CONSUMED: the spec installs
    `SkReset` and answers -`e`, and the checker accepts only at that
    model. -/
private theorem send_sound_ok_err (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (e : Int) (peer : PeerAddr) (ch : word)
    (hst : send_state sk = SendState.SendErr e peer ch)
    (H : check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs) :
    send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs) := by
  unfold check_send_on_socket at H
  simp only [hst] at H
  unfold send_on_socket
  simp only [hst]
  obtain ⟨heff, hm, hevs⟩ :=
    (check_ret_only_copyins_ok_iff pre eff (errno_ret e)
      (with_fds (fd_insert (m_fds m) fd (FdEntry.FdSocket (SockState.SkReset peer ch))) m)
      [] m' evs).mp H
  rw [heff, hm, hevs]
  exact record_copyins_ok_empty rfl (send_seqSpec_set_fds_ret_only_ok
    (fd_insert (m_fds m) fd (FdEntry.FdSocket (SockState.SkReset peer ch)))
    (errno_ret e) i m)

/-- `SendGoes ch` — the three answers that move no payload byte, then the
    delivered prefix.  The delivered arm's `choose` is inhabited by
    `bs.take ret.toNat`, which is why the checker's guard carries
    `ret ≤ total`: `send_bytes` bounds the chosen prefix by `total` and
    the checker's `ret` plays the chosen `ds.length`. -/
private theorem send_sound_ok_goes (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (ch : word)
    (hst : send_state sk = SendState.SendGoes ch)
    (H : check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs) :
    send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs) := by
  unfold check_send_on_socket at H
  simp only [hst] at H
  unfold send_on_socket
  simp only [hst]
  unfold send_bytes
  by_cases ht : w_is0 total = true
  · simp only [ht, ite_true] at H ⊢
    obtain ⟨heff, hm, hevs⟩ :=
      (check_ret_only_copyins_ok_iff pre eff (BitVec.ofInt 64 0) m [] m' evs).mp H
    rw [heff, hm, hevs]
    exact send_record_copyins_ret_only_ok pre (BitVec.ofInt 64 0) i m
  · simp only [ht, Bool.false_eq_true, ite_false] at H ⊢
    by_cases hb : (bs.length == 0) = true
    · simp only [hb, ite_true] at H ⊢
      obtain ⟨heff, hm, hevs⟩ :=
        (check_ret_only_copyins_ok_iff pre eff (errno_ret EFAULT) m [] m' evs).mp H
      rw [heff, hm, hevs]
      exact send_record_copyins_ret_only_ok pre (errno_ret EFAULT) i m
    · simp only [hb, Bool.false_eq_true, ite_false] at H ⊢
      obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
      cases ws <;> cases zs <;> cases us <;> cases cs
      · simp only [] at H
        by_cases hg : (decide (1 ≤ (ret.toNat : Int))
            && decide ((ret.toNat : Int) ≤ (bs.length : Int))
            && decide ((ret.toNat : Int) ≤ (total.toNat : Int))) = true
        · simp only [hg, ite_true] at H
          by_cases hr : access_ranges_eqb ks (pre ++ acc ret.toNat) = true
          · simp only [hr, ite_true, check_result.CheckOk.injEq] at H
            obtain ⟨rfl, rfl⟩ := H
            have hg' : decide (1 ≤ (ret.toNat : Int)) = true
                ∧ decide ((ret.toNat : Int) ≤ (bs.length : Int)) = true
                ∧ decide ((ret.toNat : Int) ≤ (total.toNat : Int)) = true := by
              simpa only [Bool.and_eq_true, and_assoc] using hg
            obtain ⟨h1, h2, h3⟩ := hg'
            have h1' : (1 : Int) ≤ (ret.toNat : Int) := of_decide_eq_true h1
            have h2' : (ret.toNat : Int) ≤ (bs.length : Int) := of_decide_eq_true h2
            have h3' : (ret.toNat : Int) ≤ (total.toNat : Int) := of_decide_eq_true h3
            have hks : ks = pre ++ acc ret.toNat :=
              (access_ranges_eqb_eq ks (pre ++ acc ret.toNat)).mp hr
            subst hks
            have hbl : ret.toNat ≤ bs.length := Int.ofNat_le.mp h2'
            have hlen : (bs.take ret.toNat).length = ret.toNat := by
              rw [List.length_take, Nat.min_eq_left hbl]
            have hlw : len_word (bs.take ret.toNat) = ret :=
              len_word_firstn_ret ret bs ⟨by omega, h2'⟩
            refine ⟨bs.take ret.toNat, m, [], (bs.take ret.toNat).map (event.WriteEv ch),
              ?_, ?_, by simp⟩
            · exact choose_ok _ _ i m
                ⟨by rw [hlen]; exact h1', by rw [hlen]; exact h3', by rw [hlen]⟩
            · simp only []
              rw [hlen, hlw]
              exact send_seqSpec_emit_record_ret_only_ok _ (pre ++ acc ret.toNat) ret i m
          · simp only [hr, Bool.false_eq_true, ite_false] at H
            exact nomatch H
        · simp only [hg, Bool.false_eq_true, ite_false] at H
          exact nomatch H
      all_goals (simp only [] at H; exact nomatch H)

/-- Soundness on accepted outcomes: whatever `check_send_on_socket`
    accepts, the relational `send_on_socket` admits, at the model the
    caller captured (both call sites run it at their own `m`). -/
theorem check_send_on_socket_sound_ok (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput)
    (H : check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs) :
    send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs) := by
  cases hst : send_state sk with
  | SendGoes ch => exact send_sound_ok_goes pre acc fd sk total bs eff m m' evs i ch hst H
  | SendErr e peer ch =>
    exact send_sound_ok_err pre acc fd sk total bs eff m m' evs i e peer ch hst H
  | SendDead => exact send_sound_ok_dead pre acc fd sk total bs eff m m' evs i hst H

/-! #### Declines: the checker has none, and neither has the spec -/

/-- Every arm of `check_send_on_socket` either accepts or rejects; none
    declines.  That is what makes the two callers' `CheckUnmodeled`
    reachable only through THEIR OWN gates. -/
theorem check_send_on_socket_no_unmodeled (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m : Model) :
    check_send_on_socket pre acc fd sk total bs eff m ≠ .CheckUnmodeled := by
  unfold check_send_on_socket
  cases hst : send_state sk with
  | SendDead =>
    exact check_ret_only_copyins_no_unmodeled pre eff (errno_ret EPIPE) m []
  | SendErr e peer ch =>
    exact check_ret_only_copyins_no_unmodeled pre eff (errno_ret e)
      (with_fds (fd_insert (m_fds m) fd (FdEntry.FdSocket (SockState.SkReset peer ch))) m) []
  | SendGoes ch =>
    by_cases ht : w_is0 total = true
    · simp only [ht, ite_true]
      exact check_ret_only_copyins_no_unmodeled pre eff (BitVec.ofInt 64 0) m []
    · simp only [ht, Bool.false_eq_true, ite_false]
      by_cases hb : (bs.length == 0) = true
      · simp only [hb, ite_true]
        exact check_ret_only_copyins_no_unmodeled pre eff (errno_ret EFAULT) m []
      · simp only [hb, Bool.false_eq_true, ite_false]
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs
        · simp only []
          by_cases hg : (decide (1 ≤ (ret.toNat : Int))
              && decide ((ret.toNat : Int) ≤ (bs.length : Int))
              && decide ((ret.toNat : Int) ≤ (total.toNat : Int))) = true
          · simp only [hg, ite_true]
            by_cases hr : access_ranges_eqb ks (pre ++ acc ret.toNat) = true
            · simp only [hr, ite_true]
              simp
            · simp only [hr, Bool.false_eq_true, ite_false]
              simp
          · simp only [hg, Bool.false_eq_true, ite_false]
            simp
        all_goals simp

/-- The same fact in the shape the two callers' statements use: a decline
    that cannot happen implies anything about the spec.  It is a
    corollary of `check_send_on_socket_no_unmodeled` rather than a
    separate walk, which is why the two names coexist: the standalone fact
    is `_no_unmodeled`, and the direction is `_sound_unmodeled`. -/
theorem check_send_on_socket_sound_unmodeled (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_send_on_socket pre acc fd sk total bs eff m = .CheckUnmodeled) :
    send_on_socket pre acc fd sk total bs m i m .unmodeled :=
  absurd H (check_send_on_socket_no_unmodeled pre acc fd sk total bs eff m)

/-- `SendDead` — -EPIPE, and `record_copyins` around a `ret_only` cannot
    decline. -/
private theorem send_no_unmodeled_dead (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (m : Model) (i : SyscallInput)
    (hst : send_state sk = SendState.SendDead)
    (H : send_on_socket pre acc fd sk total bs m i m .unmodeled) : False := by
  unfold send_on_socket at H
  simp only [hst] at H
  exact send_record_copyins_ret_only_no_unmodeled pre (errno_ret EPIPE) i m H

/-- `SendErr e peer ch` — the same, with the consumed-error stage inside the
    ledger. -/
private theorem send_no_unmodeled_err (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (m : Model) (i : SyscallInput) (e : Int) (peer : PeerAddr)
    (ch : word) (hst : send_state sk = SendState.SendErr e peer ch)
    (H : send_on_socket pre acc fd sk total bs m i m .unmodeled) : False := by
  unfold send_on_socket at H
  simp only [hst] at H
  exact send_record_copyins_set_fds_ret_only_no_unmodeled
    (fd_insert (m_fds m) fd (FdEntry.FdSocket (SockState.SkReset peer ch)))
    pre (errno_ret e) i m H

/-- `SendGoes ch` — `send_bytes`' three arms, none of which declines. -/
private theorem send_no_unmodeled_goes (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (m : Model) (i : SyscallInput) (ch : word)
    (hst : send_state sk = SendState.SendGoes ch)
    (H : send_on_socket pre acc fd sk total bs m i m .unmodeled) : False := by
  unfold send_on_socket at H
  simp only [hst] at H
  unfold send_bytes at H
  by_cases ht : w_is0 total = true
  · simp only [ht, ite_true] at H
    exact send_record_copyins_ret_only_no_unmodeled pre (BitVec.ofInt 64 0) i m H
  · simp only [ht, Bool.false_eq_true, ite_false] at H
    by_cases hb : (bs.length == 0) = true
    · simp only [hb, ite_true] at H
      exact send_record_copyins_ret_only_no_unmodeled pre (errno_ret EFAULT) i m H
    · simp only [hb, Bool.false_eq_true, ite_false] at H
      exact send_choose_deliver_no_unmodeled
        (fun ds : List byte => 1 ≤ (ds.length : Int)
          ∧ (ds.length : Int) ≤ (total.toNat : Int)
          ∧ ds = bs.take ds.length)
        (fun ds => ds.map (event.WriteEv ch))
        (fun ds => pre ++ acc ds.length) (fun ds => len_word ds) i m H

/-- `send_on_socket` never declines, so the checker's totality above is
    matched on the spec side: a `sendto`/`sendmsg` that declines does so at
    ITS OWN gates, never in the shared socket half.  That is exactly what
    makes the two calls' `complete_unmodeled` lemmas able to blame the
    gates rather than the send. -/
theorem send_on_socket_no_unmodeled (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (m : Model) (i : SyscallInput) :
    ¬ send_on_socket pre acc fd sk total bs m i m .unmodeled := by
  intro H
  cases hst : send_state sk with
  | SendDead => exact send_no_unmodeled_dead pre acc fd sk total bs m i hst H
  | SendErr e peer ch => exact send_no_unmodeled_err pre acc fd sk total bs m i e peer ch hst H
  | SendGoes ch => exact send_no_unmodeled_goes pre acc fd sk total bs m i ch hst H

/-! #### The three arms, admitted outcomes -/

/-- `SendDead` — the checker's -EPIPE leaf is exact. -/
private theorem send_complete_ok_dead (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (hst : send_state sk = SendState.SendDead)
    (H : send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs)) :
    check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs := by
  unfold send_on_socket at H
  simp only [hst] at H
  unfold check_send_on_socket
  simp only [hst]
  obtain ⟨heff, hm, hevs⟩ :=
    send_record_copyins_ret_only_ok_inv pre (errno_ret EPIPE) i m eff m' evs H
  rw [heff, hm, hevs]
  exact check_ret_only_copyins_refl pre (errno_ret EPIPE) m []

/-- `SendErr e peer ch` — the consumed error, inverted: an admitted outcome
    pins the answer to -`e` at the `SkReset` model, which is what the
    checker accepts. -/
private theorem send_complete_ok_err (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (e : Int) (peer : PeerAddr) (ch : word)
    (hst : send_state sk = SendState.SendErr e peer ch)
    (H : send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs)) :
    check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs := by
  unfold send_on_socket at H
  simp only [hst] at H
  unfold check_send_on_socket
  simp only [hst]
  obtain ⟨core, hcore, heff⟩ := record_copyins_ok_inv pre
    (seqSpec (set_fds (fd_insert (m_fds m) fd (FdEntry.FdSocket (SockState.SkReset peer ch))))
      (err_ret e)) i m eff m' evs H
  obtain ⟨u, m1, ev1, ev2, h1, h2, h3⟩ := hcore
  cases h1
  cases h2
  simp only [mkEffect, List.append_nil] at h3 heff
  rw [heff, h3]
  exact check_ret_only_copyins_refl pre (errno_ret e)
    (with_fds (fd_insert (m_fds m) fd (FdEntry.FdSocket (SockState.SkReset peer ch))) m) []

/-- `SendGoes ch` — an admitted outcome of `send_bytes` names the prefix
    `ds` the environment chose, and the checker accepts exactly the effect
    that choice produces: the claim `len_word ds` passes its guard because
    `send_bytes` bounds `ds.length` by `total` and `ds` is a prefix of the
    source. -/
private theorem send_complete_ok_goes (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (ch : word)
    (hst : send_state sk = SendState.SendGoes ch)
    (H : send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs)) :
    check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs := by
  unfold send_on_socket at H
  simp only [hst] at H
  unfold send_bytes at H
  unfold check_send_on_socket
  simp only [hst]
  by_cases ht : w_is0 total = true
  · simp only [ht, ite_true] at H ⊢
    obtain ⟨heff, hm, hevs⟩ :=
      send_record_copyins_ret_only_ok_inv pre (BitVec.ofInt 64 0) i m eff m' evs H
    rw [heff, hm, hevs]
    exact check_ret_only_copyins_refl pre (BitVec.ofInt 64 0) m []
  · simp only [ht, Bool.false_eq_true, ite_false] at H ⊢
    by_cases hb : (bs.length == 0) = true
    · simp only [hb, ite_true] at H ⊢
      obtain ⟨heff, hm, hevs⟩ :=
        send_record_copyins_ret_only_ok_inv pre (errno_ret EFAULT) i m eff m' evs H
      rw [heff, hm, hevs]
      exact check_ret_only_copyins_refl pre (errno_ret EFAULT) m []
    · simp only [hb, Bool.false_eq_true, ite_false] at H ⊢
      obtain ⟨ds, m1, evs1, evs2, h1, h2, h3⟩ := H
      obtain ⟨x, hP, hok⟩ := h1
      cases hok
      -- the environment's choice `ds` is the claim the checker will see
      obtain ⟨heff, hm, hevs⟩ :=
        send_seqSpec_emit_record_ret_only_ok_inv (ds.map (event.WriteEv ch))
          (pre ++ acc ds.length) (len_word ds) i m eff m' evs2 h2
      rw [hevs, List.nil_append] at h3
      -- the claim `len_word ds` IS `ds.length`, and `ds` is a prefix of the
      -- source, so the three bounds `send_bytes` states for `ds` are the
      -- three the checker tests on `ret`
      have hsm : (ds.length : Int) < two_pow_64 :=
        send_length_lt_two_pow_64 ds total hP.2.1
      have hlen : (len_word ds).toNat = ds.length :=
        Int.ofNat_inj.mp (len_word_unsigned ds hsm)
      have hble : (ds.length : Int) ≤ (bs.length : Int) := by
        have h : (bs.take ds.length).length ≤ bs.length := by
          rw [List.length_take]
          exact Nat.min_le_right _ _
        rw [← hP.2.2] at h
        exact_mod_cast h
      have hg : (decide (1 ≤ (ds.length : Int))
          && decide ((ds.length : Int) ≤ (bs.length : Int))
          && decide ((ds.length : Int) ≤ (total.toNat : Int))) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨by rw [decide_eq_true_eq]; exact hP.1,
                by rw [decide_eq_true_eq]; exact hble⟩,
               by rw [decide_eq_true_eq]; exact hP.2.1⟩
      have heff' : eff = ⟨len_word ds, [], [], [], [], pre ++ acc ds.length⟩ := by
        rw [heff]
        rfl
      rw [heff', hm, h3]
      simp only [hlen, hg, ite_true, access_ranges_eqb_refl]
      rw [← hP.2.2]

/-- Completeness on admitted outcomes: every outcome `send_on_socket`
    relates, `check_send_on_socket` accepts, at the same model and with
    the same events. -/
theorem check_send_on_socket_complete_ok (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput)
    (H : send_on_socket pre acc fd sk total bs m i m (.ok eff m' evs)) :
    check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs := by
  cases hst : send_state sk with
  | SendGoes ch => exact send_complete_ok_goes pre acc fd sk total bs eff m m' evs i ch hst H
  | SendErr e peer ch =>
    exact send_complete_ok_err pre acc fd sk total bs eff m m' evs i e peer ch hst H
  | SendDead => exact send_complete_ok_dead pre acc fd sk total bs eff m m' evs i hst H


/- =========================================================================
   sendto (206)
   ========================================================================= -/

/-! ### The leaves the fd dispatch ends in

  `-EBADF`, `-ENOTSOCK` and `import_ubuf`'s -EFAULT all answer through
  `check_ret_only` against the spec's `err_ret`, and the socket arm is the
  shared send body.  The first two are the public `arm_ok` / `arm_check_ok`
  of `Checks.Sys.Prelude`, opened at the top of this file and cited directly
  (the two statements that used to be restated here under a `send_` prefix
  are theirs verbatim). -/

/-- The `import_ubuf` verdict, and the fd INSIDE it.  The checker's
    `check_access_ok_zero` against the spec's `access_ok_zero`: the range
    test passes the fd dispatch through, and the range test's other answer
    is -EFAULT on both sides — which is why `sendto(-1, unmapped, n, …)`
    is -EFAULT rather than -EBADF. -/
private theorem sendto_body_sound_ok (fd buf count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_access_ok_zero buf count eff m
      (match fd_lookup (m_fds m) fd with
       | none => check_ret_only eff (errno_ret EBADF) m []
       | some (.FdSocket sk) =>
           check_send_on_socket [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes i.in_mem buf count) eff m
       | some _ => check_ret_only eff (errno_ret ENOTSOCK) m [])
      = .CheckOk m' evs) :
    access_ok_zero buf count
      (match fd_lookup (m_fds m) fd with
       | none => err_ret EBADF
       | some (.FdSocket sk) =>
           send_on_socket [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes i.in_mem buf count) m
       | some _ => err_ret ENOTSOCK) i m (.ok eff m' evs) := by
  unfold check_access_ok_zero at H
  unfold access_ok_zero
  by_cases hok : access_okb buf (count.toNat : Int) = true
  · simp only [hok, ite_true] at H ⊢
    generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
    cases ent with
    | none => exact arm_ok (errno_ret EBADF) eff m m' evs i H
    | some e =>
      cases e <;>
        (simp only [] at H ⊢
         first
        | exact check_send_on_socket_sound_ok [] (fun n => [(buf, n)]) fd _
            count (readable_bytes i.in_mem buf count) eff m m' evs i H
         | exact arm_ok (errno_ret ENOTSOCK) eff m m' evs i H)
  · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
    exact arm_ok (errno_ret EFAULT) eff m m' evs i H

/-- Soundness on accepted outcomes: whatever `check_sendto` accepts, the
    relational `sendto_spec` admits.  The walk is the kernel's own order —
    the three model gates, then `import_ubuf`'s verdict, then the fd — and
    the fd dispatch stays inside the verdict. -/
theorem check_sendto_sound_ok (i : SyscallInput) (fd buf count flags addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sendto i fd buf count flags addrp eff m = .CheckOk m' evs) :
    sendto_spec fd buf count flags addrp addrlen i m (.ok eff m' evs) := by
  unfold check_sendto at H
  unfold sendto_spec
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
    exact nomatch H
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    by_cases ha : (!(w_is0 addrp)) = true
    · simp only [ha, ite_true] at H ⊢
      exact nomatch H
    · simp only [ha, Bool.false_eq_true, ite_false] at H ⊢
      by_cases hc : (!(modeled_rw_count count)) = true
      · simp only [hc, ite_true] at H ⊢
        exact nomatch H
      · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
        refine bind_ok0 inputSpec _ i m i m eff m' evs (input_ok i m) ?_
        refine bind_ok0 getModelSpec _ i m m m eff m' evs (getModel_ok i m) ?_
        exact sendto_body_sound_ok fd buf count eff m m' evs i H

/-- Soundness on declines.  `check_sendto` declines only at its three
    gates, so a decline IS one of them — the fd dispatch and the shared
    send body cannot produce one. -/
theorem check_sendto_sound_unmodeled (i : SyscallInput)
    (fd buf count flags addrp addrlen : word) (eff : SyscallEffect) (m : Model)
    (H : check_sendto i fd buf count flags addrp eff m = .CheckUnmodeled) :
    sendto_spec fd buf count flags addrp addrlen i m .unmodeled := by
  unfold check_sendto at H
  unfold sendto_spec
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
    exact unmodeled_intro i m
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    by_cases ha : (!(w_is0 addrp)) = true
    · simp only [ha, ite_true] at H ⊢
      exact unmodeled_intro i m
    · simp only [ha, Bool.false_eq_true, ite_false] at H ⊢
      by_cases hc : (!(modeled_rw_count count)) = true
      · simp only [hc, ite_true] at H ⊢
        exact unmodeled_intro i m
      · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
        refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
        refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
        unfold check_access_ok_zero at H
        unfold access_ok_zero
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · simp only [hok, ite_true] at H ⊢
          generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
          cases ent with
          | none =>
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
          | some e =>
            cases e <;>
              (simp only [] at H ⊢
               first
              | exact check_send_on_socket_sound_unmodeled [] (fun n => [(buf, n)]) fd _
                  count (readable_bytes i.in_mem buf count) eff m i H
               | exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTSOCK) m []))
        · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])

/-- Completeness on admitted outcomes: every outcome `sendto_spec` relates,
    `check_sendto` accepts, at the same model and with the same events.
    Each of the three gates' declines is refuted by inversion, so the walk
    reaches the fd dispatch. -/
theorem check_sendto_complete_ok (i : SyscallInput)
    (fd buf count flags addrp addrlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : sendto_spec fd buf count flags addrp addrlen i m (.ok eff m' evs)) :
    check_sendto i fd buf count flags addrp eff m = .CheckOk m' evs := by
  unfold check_sendto
  unfold sendto_spec at H
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
    exact nomatch H
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    by_cases ha : (!(w_is0 addrp)) = true
    · simp only [ha, ite_true] at H ⊢
      exact nomatch H
    · simp only [ha, Bool.false_eq_true, ite_false] at H ⊢
      by_cases hc : (!(modeled_rw_count count)) = true
      · simp only [hc, ite_true] at H ⊢
        exact nomatch H
      · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
        simp only [inputSpec, getModelSpec] at H
        have H := bind_input_model_inv
          (A := SyscallEffect)
          (k := fun (i0 : SyscallInput) (m0 : Model) => access_ok_zero buf count
            (match fd_lookup (m_fds m0) fd with
             | none => err_ret EBADF
             | some (.FdSocket sk) =>
                 send_on_socket [] (fun n => [(buf, n)]) fd sk count
                   (readable_bytes i0.in_mem buf count) m0
             | some _ => err_ret ENOTSOCK)) i m (.ok eff m' evs) H
        unfold access_ok_zero at H
        unfold check_access_ok_zero
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · simp only [hok, ite_true] at H ⊢
          generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
          cases ent with
          | none => exact arm_check_ok (errno_ret EBADF) eff m m' evs i H
          | some e =>
            cases e <;>
              (simp only [] at H ⊢
               first
              | exact check_send_on_socket_complete_ok [] (fun n => [(buf, n)]) fd _
                  count (readable_bytes i.in_mem buf count) eff m m' evs i H
               | exact arm_check_ok (errno_ret ENOTSOCK) eff m m' evs i H)
        · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
          exact arm_check_ok (errno_ret EFAULT) eff m m' evs i H

/-- Completeness on declines: wherever `sendto_spec` fails closed, so does
    `check_sendto`.  The three gates answer `rfl`; past them only the
    shared send body could decline, and it cannot. -/
theorem check_sendto_complete_unmodeled (i : SyscallInput)
    (fd buf count flags addrp addrlen : word) (m : Model) (eff : SyscallEffect)
    (H : sendto_spec fd buf count flags addrp addrlen i m .unmodeled) :
    check_sendto i fd buf count flags addrp eff m = .CheckUnmodeled := by
  unfold check_sendto
  unfold sendto_spec at H
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    by_cases ha : (!(w_is0 addrp)) = true
    · simp only [ha, ite_true] at H ⊢
    · simp only [ha, Bool.false_eq_true, ite_false] at H ⊢
      by_cases hc : (!(modeled_rw_count count)) = true
      · simp only [hc, ite_true] at H ⊢
      · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
        simp only [inputSpec, getModelSpec] at H
        have H := bind_input_model_inv
          (fun (i0 : SyscallInput) (m0 : Model) => access_ok_zero buf count
            (match fd_lookup (m_fds m0) fd with
             | none => err_ret EBADF
             | some (.FdSocket sk) =>
                 send_on_socket [] (fun n => [(buf, n)]) fd sk count
                   (readable_bytes i0.in_mem buf count) m0
             | some _ => err_ret ENOTSOCK)) i m .unmodeled H
        unfold access_ok_zero at H
        unfold check_access_ok_zero
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · simp only [hok, ite_true] at H ⊢
          generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
          cases ent with
          | none =>
            exact absurd H (ret_only_ne_unmodeled (errno_ret EBADF) i m)
          | some e =>
            cases e <;>
              (simp only [] at H ⊢
               first
              | exact absurd H (send_on_socket_no_unmodeled [] (fun n => [(buf, n)]) fd _
                  count (readable_bytes i.in_mem buf count) m i)
               | exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTSOCK) i m))
        · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
          exact absurd H (ret_only_ne_unmodeled (errno_ret EFAULT) i m)

/- =========================================================================
   sendmsg (211)
   ========================================================================= -/

/-! ### The arms of `check_sendmsg`, named

  `check_sendmsg`'s socket arm is thirty lines of six `read_u64`s, an
  iovec import and five gates, and the fd dispatch in front of it is
  another ten.  A proof that carries that body through every case split is
  what the kernel rejects (see the file header), so the two arms are
  named once here and the lemmas below dispatch over the NAMES: the
  definitions are copies of the parent's text, and every use of them is
  through a definitional-equality step (`exact H` against a stated type,
  or `sendmsg_check_all` unfolded at the one place the dispatcher needs
  it), so a later edit to the parent's body stops this file compiling
  rather than silently detaching from it.

  `sendmsg_check_body` / `sendmsg_spec_body` are the SOCKET arm alone,
  after the fd lookup; `sendmsg_check_all` / `sendmsg_spec_all` are the
  whole body after the flag gate, fd dispatch included. -/

/-- The socket arm of `check_sendmsg` (parent lines 519-566):
    the 56-byte header, the six fields, then the import and the send. -/
private def sendmsg_check_body (i : SyscallInput) (fd msgp : word) (sk : SockState)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) with
  | none => check_ret_only eff (errno_ret EFAULT) m []
  | some _ =>
      match read_u64 i.in_mem msgp,
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 8),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 16),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 24),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 32),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) with
      | some name, some _, some iov, some iovlen, some _, some ctllen =>
          if !(w_is0 name) then .CheckUnmodeled
          else if decide (IOV_MAX < (iovlen.toNat : Int))
          then check_ret_only_copyins [(msgp, MSGHDR_SIZE.toNat)] eff
                 (errno_ret EMSGSIZE) m []
          else if decide (UIO_FASTIOV < (iovlen.toNat : Int)) then .CheckUnmodeled
          else
          match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
          | .ImpFault =>
              check_ret_only_copyins
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                eff (errno_ret EFAULT) m []
          | .ImpInval =>
              check_ret_only_copyins
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                eff (errno_ret EINVAL) m []
          | .ImpOk iovs0 =>
              -- msg_controllen is decided HERE, where ____sys_sendmsg
              -- decides it: after the descriptors are imported, not
              -- before.  Ordering is behaviour — a call with a
              -- non-zero controllen AND iovlen over IOV_MAX answers
              -- -EMSGSIZE above rather than declining here.
              if !(w_is0 ctllen) then .CheckUnmodeled
              else if !(decide (iovs_total (cap_iovecs iovs0) ≤ rw_bytes_max))
              then .CheckUnmodeled
              else
              check_send_on_socket
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                fd sk
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))
                (writev_gathered i.in_mem iovs0) eff m
      | _, _, _, _, _, _ =>
          check_ret_only_copyins [(msgp, MSGHDR_SIZE.toNat)] eff
            (errno_ret EFAULT) m []

/-- The socket arm of `sendmsg_spec` (parent lines 2006-2082),
    the same walk with the spec's leaves.  The two `let`s the parent writes
    for `msg_namelen` and `msg_control` are dropped: they are zeta, and
    `unfold` removes them on the other side of every equation below. -/
private def sendmsg_spec_body (i : SyscallInput) (fd msgp : word) (sk : SockState)
    (m : Model) : SysSpec SyscallEffect :=
  match read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) with
  | none => err_ret EFAULT
  | some _ =>
      match read_u64 i.in_mem msgp,
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 8),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 16),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 24),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 32),
            read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) with
      | some name, some namelen, some iov, some iovlen, some ctl, some ctllen =>
          let _ := namelen
          let _ := ctl
          if !(w_is0 name) then unmodeled
          else if decide (IOV_MAX < (iovlen.toNat : Int))
          then record_copyins [(msgp, MSGHDR_SIZE.toNat)] (err_ret EMSGSIZE)
          else if decide (UIO_FASTIOV < (iovlen.toNat : Int)) then unmodeled
          else
          match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
          | .ImpFault =>
              record_copyins
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                (err_ret EFAULT)
          | .ImpInval =>
              record_copyins
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                (err_ret EINVAL)
          | .ImpOk iovs0 =>
              if !(w_is0 ctllen) then unmodeled
              else if !decide (iovs_total (cap_iovecs iovs0) ≤ rw_bytes_max)
              then unmodeled
              else
              send_on_socket
                ([(msgp, MSGHDR_SIZE.toNat)]
                 ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                fd sk
                (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))
                (writev_gathered i.in_mem iovs0) m
      | _, _, _, _, _, _ =>
          record_copyins [(msgp, MSGHDR_SIZE.toNat)] (err_ret EFAULT)

/-- `check_sendmsg`'s body after the flag gate: the fd
    dispatch, whose socket arm is `sendmsg_check_body`. -/
private def sendmsg_check_all (i : SyscallInput) (fd msgp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) | some (.FdFile _ _)
  | some (.FdFileW _ _) | some .FdDir
  | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some (.FdPipe _ _) | some (.FdDevNull _ _) | some .FdUrandom =>
      check_ret_only eff (errno_ret ENOTSOCK) m []
  | some (.FdSocket sk) => sendmsg_check_body i fd msgp sk eff m

/-- `sendmsg_spec`'s body after the flag gate, the same
    dispatch with the spec's socket arm. -/
private def sendmsg_spec_all (i : SyscallInput) (fd msgp : word)
    (m : Model) : SysSpec SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (FdEntry.FdChannel _) | some (FdEntry.FdFile _ _)
  | some (FdEntry.FdFileW _ _) | some (FdEntry.FdFileA _ _)
  | some (FdEntry.FdFileRW _ _)
  | some FdEntry.FdDir
  | some (FdEntry.FdPipe _ _)
  | some (FdEntry.FdDevNull _ _)
  | some FdEntry.FdUrandom =>
      err_ret ENOTSOCK
  | some (FdEntry.FdSocket sk) => sendmsg_spec_body i fd msgp sk m

/-- The socket arm, accepted outcomes.  The header read decides -EFAULT on
    both sides; the six field reads are then peeled ONE AT A TIME, and the
    six shapes that are not all-`some` are the total-match -EFAULT arm the
    checker and the spec spell the same way (`__copy_msghdr` reads the
    fields it needs and the arm answers with the header alone recorded);
    past them the gates are walked in the kernel's order and the send is
    handed to the shared body. -/
private theorem sendmsg_socket_sound_ok (i : SyscallInput) (fd msgp : word)
    (sk : SockState) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : sendmsg_check_body i fd msgp sk eff m = .CheckOk m' evs) :
    sendmsg_spec_body i fd msgp sk m i m (.ok eff m' evs) := by
  unfold sendmsg_check_body at H
  unfold sendmsg_spec_body
  generalize hrb : read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) = rb at H ⊢
  cases rb with
  | none =>
    simp only [] at H ⊢
    exact arm_ok (errno_ret EFAULT) eff m m' evs i H
  | some hdr =>
    simp only [] at H ⊢
    generalize h0 : read_u64 i.in_mem msgp = r0 at H ⊢
    cases r0 with
    | none =>
      simp only [] at H ⊢
      exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
    | some name =>
      generalize h1 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 8) = r1 at H ⊢
      cases r1 with
      | none =>
        simp only [] at H ⊢
        exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
      | some namelen =>
        generalize h2 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 16) = r2 at H ⊢
        cases r2 with
        | none =>
          simp only [] at H ⊢
          exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
        | some iov =>
          generalize h3 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 24) = r3 at H ⊢
          cases r3 with
          | none =>
            simp only [] at H ⊢
            exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
          | some iovlen =>
            generalize h4 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 32) = r4 at H ⊢
            cases r4 with
            | none =>
              simp only [] at H ⊢
              exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
            | some ctl =>
              generalize h5 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) = r5 at H ⊢
              cases r5 with
              | none =>
                simp only [] at H ⊢
                exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
              | some ctllen =>
                simp only [] at H ⊢
                by_cases hn : (!(w_is0 name)) = true
                · simp only [hn, ite_true] at H ⊢
                  exact nomatch H
                · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
                  by_cases hiv : decide (IOV_MAX < (iovlen.toNat : Int)) = true
                  · simp only [hiv, ite_true] at H ⊢
                    exact arm_copyins_ok _ (errno_ret EMSGSIZE) eff m m' evs i H
                  · simp only [hiv, Bool.false_eq_true, ite_false] at H ⊢
                    by_cases hfa : decide (UIO_FASTIOV < (iovlen.toNat : Int)) = true
                    · simp only [hfa, ite_true] at H ⊢
                      exact nomatch H
                    · simp only [hfa, Bool.false_eq_true, ite_false] at H ⊢
                      generalize hci : copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ci at H ⊢
                      cases ci with
                      | ImpFault =>
                        simp only [] at H ⊢
                        exact arm_copyins_ok _ (errno_ret EFAULT) eff m m' evs i H
                      | ImpInval =>
                        simp only [] at H ⊢
                        exact arm_copyins_ok _ (errno_ret EINVAL) eff m m' evs i H
                      | ImpOk iovs0 =>
                        simp only [] at H ⊢
                        by_cases hcl : (!(w_is0 ctllen)) = true
                        · simp only [hcl, ite_true] at H ⊢
                          exact nomatch H
                        · simp only [hcl, Bool.false_eq_true, ite_false] at H ⊢
                          by_cases hmt : (!(decide (iovs_total (cap_iovecs iovs0)
                              ≤ rw_bytes_max))) = true
                          · simp only [hmt, ite_true] at H ⊢
                            exact nomatch H
                          · simp only [hmt, Bool.false_eq_true, ite_false] at H ⊢
                            exact check_send_on_socket_sound_ok _ _ fd sk _ _ eff m m' evs i H

/-- The socket arm, declines: the four gates that decline on both sides at
    once (`msg_name`, the heap-backed `iovlen`, `msg_controllen`, the
    `rw_bytes_max` gather) answer `unmodeled` on both sides, and every
    other leaf cannot decline. -/
private theorem sendmsg_socket_sound_unmodeled (i : SyscallInput) (fd msgp : word)
    (sk : SockState) (eff : SyscallEffect) (m : Model)
    (H : sendmsg_check_body i fd msgp sk eff m = .CheckUnmodeled) :
    sendmsg_spec_body i fd msgp sk m i m .unmodeled := by
  unfold sendmsg_check_body at H
  unfold sendmsg_spec_body
  generalize hrb : read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) = rb at H ⊢
  cases rb with
  | none =>
    simp only [] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
  | some hdr =>
    simp only [] at H ⊢
    generalize h0 : read_u64 i.in_mem msgp = r0 at H ⊢
    cases r0 with
    | none =>
      simp only [] at H ⊢
      exact absurd H
        (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
    | some name =>
      generalize h1 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 8) = r1 at H ⊢
      cases r1 with
      | none =>
        simp only [] at H ⊢
        exact absurd H
          (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
      | some namelen =>
        generalize h2 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 16) = r2 at H ⊢
        cases r2 with
        | none =>
          simp only [] at H ⊢
          exact absurd H
            (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
        | some iov =>
          generalize h3 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 24) = r3 at H ⊢
          cases r3 with
          | none =>
            simp only [] at H ⊢
            exact absurd H
              (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
          | some iovlen =>
            generalize h4 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 32) = r4 at H ⊢
            cases r4 with
            | none =>
              simp only [] at H ⊢
              exact absurd H
                (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
            | some ctl =>
              generalize h5 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) = r5 at H ⊢
              cases r5 with
              | none =>
                simp only [] at H ⊢
                exact absurd H
                  (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
              | some ctllen =>
                simp only [] at H ⊢
                by_cases hn : (!(w_is0 name)) = true
                · simp only [hn, ite_true] at H ⊢
                  exact unmodeled_intro i m
                · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
                  by_cases hiv : decide (IOV_MAX < (iovlen.toNat : Int)) = true
                  · simp only [hiv, ite_true] at H ⊢
                    exact absurd H
                      (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EMSGSIZE) m [])
                  · simp only [hiv, Bool.false_eq_true, ite_false] at H ⊢
                    by_cases hfa : decide (UIO_FASTIOV < (iovlen.toNat : Int)) = true
                    · simp only [hfa, ite_true] at H ⊢
                      exact unmodeled_intro i m
                    · simp only [hfa, Bool.false_eq_true, ite_false] at H ⊢
                      generalize hci : copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ci at H ⊢
                      cases ci with
                      | ImpFault =>
                        simp only [] at H ⊢
                        exact absurd H
                          (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
                      | ImpInval =>
                        simp only [] at H ⊢
                        exact absurd H
                          (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EINVAL) m [])
                      | ImpOk iovs0 =>
                        simp only [] at H ⊢
                        by_cases hcl : (!(w_is0 ctllen)) = true
                        · simp only [hcl, ite_true] at H ⊢
                          exact unmodeled_intro i m
                        · simp only [hcl, Bool.false_eq_true, ite_false] at H ⊢
                          by_cases hmt : (!(decide (iovs_total (cap_iovecs iovs0)
                              ≤ rw_bytes_max))) = true
                          · simp only [hmt, ite_true] at H ⊢
                            exact unmodeled_intro i m
                          · simp only [hmt, Bool.false_eq_true, ite_false] at H ⊢
                            exact check_send_on_socket_sound_unmodeled _ _ fd sk _ _ eff m i H

/-- The socket arm, admitted outcomes: every shape `sendmsg_spec` can take
    here, inverted.  The two import errnos carry the header AND the
    descriptors `copy_iovecs_accesses` walked, which is why their leaves
    are stated at `arm_copyins_check_ok`'s general `reads`. -/
private theorem sendmsg_socket_complete_ok (i : SyscallInput) (fd msgp : word)
    (sk : SockState) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : sendmsg_spec_body i fd msgp sk m i m (.ok eff m' evs)) :
    sendmsg_check_body i fd msgp sk eff m = .CheckOk m' evs := by
  unfold sendmsg_check_body
  unfold sendmsg_spec_body at H
  generalize hrb : read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) = rb at H ⊢
  cases rb with
  | none =>
    simp only [] at H ⊢
    exact arm_check_ok (errno_ret EFAULT) eff m m' evs i H
  | some hdr =>
    simp only [] at H ⊢
    generalize h0 : read_u64 i.in_mem msgp = r0 at H ⊢
    cases r0 with
    | none =>
      simp only [] at H ⊢
      exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
    | some name =>
      generalize h1 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 8) = r1 at H ⊢
      cases r1 with
      | none =>
        simp only [] at H ⊢
        exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
      | some namelen =>
        generalize h2 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 16) = r2 at H ⊢
        cases r2 with
        | none =>
          simp only [] at H ⊢
          exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
        | some iov =>
          generalize h3 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 24) = r3 at H ⊢
          cases r3 with
          | none =>
            simp only [] at H ⊢
            exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
          | some iovlen =>
            generalize h4 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 32) = r4 at H ⊢
            cases r4 with
            | none =>
              simp only [] at H ⊢
              exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
            | some ctl =>
              generalize h5 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) = r5 at H ⊢
              cases r5 with
              | none =>
                simp only [] at H ⊢
                exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
              | some ctllen =>
                simp only [] at H ⊢
                by_cases hn : (!(w_is0 name)) = true
                · simp only [hn, ite_true] at H ⊢
                  exact nomatch H
                · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
                  by_cases hiv : decide (IOV_MAX < (iovlen.toNat : Int)) = true
                  · simp only [hiv, ite_true] at H ⊢
                    exact arm_copyins_check_ok _ (errno_ret EMSGSIZE) eff m m' evs i H
                  · simp only [hiv, Bool.false_eq_true, ite_false] at H ⊢
                    by_cases hfa : decide (UIO_FASTIOV < (iovlen.toNat : Int)) = true
                    · simp only [hfa, ite_true] at H ⊢
                      exact nomatch H
                    · simp only [hfa, Bool.false_eq_true, ite_false] at H ⊢
                      generalize hci : copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ci at H ⊢
                      cases ci with
                      | ImpFault =>
                        simp only [] at H ⊢
                        exact arm_copyins_check_ok _ (errno_ret EFAULT) eff m m' evs i H
                      | ImpInval =>
                        simp only [] at H ⊢
                        exact arm_copyins_check_ok _ (errno_ret EINVAL) eff m m' evs i H
                      | ImpOk iovs0 =>
                        simp only [] at H ⊢
                        by_cases hcl : (!(w_is0 ctllen)) = true
                        · simp only [hcl, ite_true] at H ⊢
                          exact nomatch H
                        · simp only [hcl, Bool.false_eq_true, ite_false] at H ⊢
                          by_cases hmt : (!(decide (iovs_total (cap_iovecs iovs0)
                              ≤ rw_bytes_max))) = true
                          · simp only [hmt, ite_true] at H ⊢
                            exact nomatch H
                          · simp only [hmt, Bool.false_eq_true, ite_false] at H ⊢
                            exact check_send_on_socket_complete_ok _ _ fd sk _ _ eff m m' evs i H

/-- The socket arm, declines: only the four both-sides gates can decline,
    and each of them answers `CheckUnmodeled` on the checker's side. -/
private theorem sendmsg_socket_complete_unmodeled (i : SyscallInput) (fd msgp : word)
    (sk : SockState) (m : Model) (eff : SyscallEffect)
    (H : sendmsg_spec_body i fd msgp sk m i m .unmodeled) :
    sendmsg_check_body i fd msgp sk eff m = .CheckUnmodeled := by
  unfold sendmsg_check_body
  unfold sendmsg_spec_body at H
  generalize hrb : read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) = rb at H ⊢
  cases rb with
  | none =>
    simp only [] at H ⊢
    exact absurd H (ret_only_ne_unmodeled (errno_ret EFAULT) i m)
  | some hdr =>
    simp only [] at H ⊢
    generalize h0 : read_u64 i.in_mem msgp = r0 at H ⊢
    cases r0 with
    | none =>
      simp only [] at H ⊢
      exact absurd H
        (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
    | some name =>
      generalize h1 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 8) = r1 at H ⊢
      cases r1 with
      | none =>
        simp only [] at H ⊢
        exact absurd H
          (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
      | some namelen =>
        generalize h2 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 16) = r2 at H ⊢
        cases r2 with
        | none =>
          simp only [] at H ⊢
          exact absurd H
            (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
        | some iov =>
          generalize h3 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 24) = r3 at H ⊢
          cases r3 with
          | none =>
            simp only [] at H ⊢
            exact absurd H
              (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
          | some iovlen =>
            generalize h4 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 32) = r4 at H ⊢
            cases r4 with
            | none =>
              simp only [] at H ⊢
              exact absurd H
                (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
            | some ctl =>
              generalize h5 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) = r5 at H ⊢
              cases r5 with
              | none =>
                simp only [] at H ⊢
                exact absurd H
                  (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
              | some ctllen =>
                simp only [] at H ⊢
                by_cases hn : (!(w_is0 name)) = true
                · simp only [hn, ite_true] at H ⊢
                · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
                  by_cases hiv : decide (IOV_MAX < (iovlen.toNat : Int)) = true
                  · simp only [hiv, ite_true] at H ⊢
                    exact absurd H
                      (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EMSGSIZE) i m)
                  · simp only [hiv, Bool.false_eq_true, ite_false] at H ⊢
                    by_cases hfa : decide (UIO_FASTIOV < (iovlen.toNat : Int)) = true
                    · simp only [hfa, ite_true] at H ⊢
                    · simp only [hfa, Bool.false_eq_true, ite_false] at H ⊢
                      generalize hci : copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = ci at H ⊢
                      cases ci with
                      | ImpFault =>
                        simp only [] at H ⊢
                        exact absurd H
                          (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EFAULT) i m)
                      | ImpInval =>
                        simp only [] at H ⊢
                        exact absurd H
                          (send_record_copyins_ret_only_no_unmodeled _ (errno_ret EINVAL) i m)
                      | ImpOk iovs0 =>
                        simp only [] at H ⊢
                        by_cases hcl : (!(w_is0 ctllen)) = true
                        · simp only [hcl, ite_true] at H ⊢
                        · simp only [hcl, Bool.false_eq_true, ite_false] at H ⊢
                          by_cases hmt : (!(decide (iovs_total (cap_iovecs iovs0)
                              ≤ rw_bytes_max))) = true
                          · simp only [hmt, ite_true] at H ⊢
                          · simp only [hmt, Bool.false_eq_true, ite_false] at H ⊢
                            exact absurd H
                              (send_on_socket_no_unmodeled _ _ fd sk _ _ m i)

/-! #### The fd dispatch, and the four public lemmas

  Each `sendmsg_all_*` lemma splits the descriptor once (`generalize` the
  lookup, `cases` the result, reduce the match) and hands the socket arm
  to the lemma above; the four public lemmas below then peel the flag gate
  and the `input`/`get_model` prologue and hand the rest to those.  That
  is the whole of the dispatcher: no proof in this section carries the
  socket arm's body through more than one split. -/

private theorem sendmsg_all_sound_ok (i : SyscallInput) (fd msgp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : sendmsg_check_all i fd msgp eff m = .CheckOk m' evs) :
    sendmsg_spec_all i fd msgp m i m (.ok eff m' evs) := by
  unfold sendmsg_check_all at H
  unfold sendmsg_spec_all
  generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
  cases ent with
  | none => exact arm_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e <;>
      (simp only [] at H ⊢
       first
       | exact sendmsg_socket_sound_ok i fd msgp _ eff m m' evs H
       | exact arm_ok (errno_ret ENOTSOCK) eff m m' evs i H)

private theorem sendmsg_all_sound_unmodeled (i : SyscallInput) (fd msgp : word)
    (eff : SyscallEffect) (m : Model)
    (H : sendmsg_check_all i fd msgp eff m = .CheckUnmodeled) :
    sendmsg_spec_all i fd msgp m i m .unmodeled := by
  unfold sendmsg_check_all at H
  unfold sendmsg_spec_all
  generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
  cases ent with
  | none =>
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e <;>
      (simp only [] at H ⊢
       first
       | exact sendmsg_socket_sound_unmodeled i fd msgp _ eff m H
       | exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTSOCK) m []))

private theorem sendmsg_all_complete_ok (i : SyscallInput) (fd msgp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : sendmsg_spec_all i fd msgp m i m (.ok eff m' evs)) :
    sendmsg_check_all i fd msgp eff m = .CheckOk m' evs := by
  unfold sendmsg_check_all
  unfold sendmsg_spec_all at H
  generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
  cases ent with
  | none => exact arm_check_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e <;>
      (simp only [] at H ⊢
       first
       | exact sendmsg_socket_complete_ok i fd msgp _ eff m m' evs H
       | exact arm_check_ok (errno_ret ENOTSOCK) eff m m' evs i H)

private theorem sendmsg_all_complete_unmodeled (i : SyscallInput) (fd msgp : word)
    (m : Model) (eff : SyscallEffect)
    (H : sendmsg_spec_all i fd msgp m i m .unmodeled) :
    sendmsg_check_all i fd msgp eff m = .CheckUnmodeled := by
  unfold sendmsg_check_all
  unfold sendmsg_spec_all at H
  generalize hfd : fd_lookup (m_fds m) fd = ent at H ⊢
  cases ent with
  | none =>
    exact absurd H (ret_only_ne_unmodeled (errno_ret EBADF) i m)
  | some e =>
    cases e <;>
      (simp only [] at H ⊢
       first
       | exact sendmsg_socket_complete_unmodeled i fd msgp _ m eff H
       | exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTSOCK) i m))

/-- Soundness on accepted outcomes: whatever `check_sendmsg` accepts, the
    relational `sendmsg_spec` admits.  The flag gate first, then the
    fd-and-header walk, which is the OPPOSITE nesting to `sendto`'s. -/
theorem check_sendmsg_sound_ok (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sendmsg i fd msgp flags eff m = .CheckOk m' evs) :
    sendmsg_spec fd msgp flags i m (.ok eff m' evs) := by
  unfold check_sendmsg at H
  unfold sendmsg_spec
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
    exact nomatch H
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    have Hc : sendmsg_check_all i fd msgp eff m = .CheckOk m' evs := H
    have Hs := sendmsg_all_sound_ok i fd msgp eff m m' evs Hc
    refine bind_ok0 inputSpec _ i m i m eff m' evs (input_ok i m) ?_
    refine bind_ok0 getModelSpec _ i m m m eff m' evs (getModel_ok i m) ?_
    exact Hs

/-- Soundness on declines.  `check_sendmsg` declines at its flag gate and
    then only where the spec declines at the same point: `msg_name`, the
    heap-backed `iovlen`, `msg_controllen` and the `rw_bytes_max` gather. -/
theorem check_sendmsg_sound_unmodeled (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_sendmsg i fd msgp flags eff m = .CheckUnmodeled) :
    sendmsg_spec fd msgp flags i m .unmodeled := by
  unfold check_sendmsg at H
  unfold sendmsg_spec
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
    exact unmodeled_intro i m
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    have Hc : sendmsg_check_all i fd msgp eff m = .CheckUnmodeled := H
    refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
    refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
    exact sendmsg_all_sound_unmodeled i fd msgp eff m Hc

/-- Completeness on admitted outcomes: every outcome `sendmsg_spec` relates,
    `check_sendmsg` accepts, at the same model and with the same events. -/
theorem check_sendmsg_complete_ok (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : sendmsg_spec fd msgp flags i m (.ok eff m' evs)) :
    check_sendmsg i fd msgp flags eff m = .CheckOk m' evs := by
  unfold check_sendmsg
  unfold sendmsg_spec at H
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
    exact nomatch H
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    simp only [inputSpec, getModelSpec] at H
    have Hs := bind_input_model_inv
      (fun (i0 : SyscallInput) (m0 : Model) => sendmsg_spec_all i0 fd msgp m0)
      i m (.ok eff m' evs) H
    exact sendmsg_all_complete_ok i fd msgp eff m m' evs Hs

/-- Completeness on declines: wherever `sendmsg_spec` fails closed,
    `check_sendmsg` does too. -/
theorem check_sendmsg_complete_unmodeled (i : SyscallInput) (fd msgp flags : word)
    (m : Model) (eff : SyscallEffect)
    (H : sendmsg_spec fd msgp flags i m .unmodeled) :
    check_sendmsg i fd msgp flags eff m = .CheckUnmodeled := by
  unfold check_sendmsg
  unfold sendmsg_spec at H
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true] at H ⊢
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    simp only [inputSpec, getModelSpec] at H
    have Hs := bind_input_model_inv
      (fun (i0 : SyscallInput) (m0 : Model) => sendmsg_spec_all i0 fd msgp m0)
      i m .unmodeled H
    exact sendmsg_all_complete_unmodeled i fd msgp m eff Hs

end LinuxSem.Checks.Sys.Net.Socket




