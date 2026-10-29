/-
  * Common.TargetCover — interval-cover dispatch for a per-payload-length-class proof.

  A phase proved per PAYLOAD-LENGTH CLASS `lo <= n <= hi`: a class theorem has
  the form `TPgen Q lo hi` = `forall n, lo <= n <= hi -> Q n` for the image's
  class predicate `Q` (e.g. "every target_pre configuration whose payload
  length is n realizes t_target").  `tp_dispatch`: a list of proved classes
  whose intervals cover `lo, hi` (reflective check `tp_covers`, by
  `vm_compute`) proves `TPgen Q lo hi`.  Stdlib only; `Q` is abstract.
  `vm_compute` sanity goals become `by decide`.
-/

namespace LinuxSem.Common.TargetCover

/-- `TPgen Q lo hi` — the per-payload-length-class statement: every length in
    `[lo, hi]` satisfies `Q`. -/
def TPgen (Q : Int → Prop) (lo hi : Int) : Prop := ∀ n, lo ≤ n ∧ n ≤ hi → Q n

/-- A proved class. -/
structure tpc (Q : Int → Prop) : Type where
  /-- Lower end of the class interval. -/
  c_lo : Int
  /-- Upper end of the class interval. -/
  c_hi : Int
  /-- The class itself. -/
  c_ok : TPgen Q c_lo c_hi

/-- `tp_covers ivs lo hi`: the intervals (sorted by lower end) cover `[lo, hi]`. -/
def tp_covers : List (Int × Int) → Int → Int → Bool
  | [], lo, hi => decide (hi < lo)
  | (a, b) :: rest, lo, hi =>
      decide (hi < lo) || (decide (a ≤ lo) && tp_covers rest (max lo (b + 1)) hi)

/-- A covering list of intervals covers every point of `[lo, hi]`: some
    interval of the list contains it. -/
theorem tp_covers_sound : ∀ (ivs : List (Int × Int)) (lo hi x : Int),
    tp_covers ivs lo hi = true → lo ≤ x ∧ x ≤ hi →
    ∃ ab, ab ∈ ivs ∧ ab.1 ≤ x ∧ x ≤ ab.2 := by
  intro ivs
  induction ivs with
  | nil =>
    intro lo hi x hc hx
    simp [tp_covers] at hc
    omega
  | cons hd rest ih =>
    intro lo hi x hc hx
    obtain ⟨a, b⟩ := hd
    simp only [tp_covers, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | ⟨ha, hr⟩
    · omega
    · by_cases hxb : x ≤ b
      · exact ⟨(a, b), List.mem_cons_self .., by omega, hxb⟩
      · have hmax : max lo (b + 1) ≤ x := by omega
        obtain ⟨ab, hin, h1, h2⟩ := ih (max lo (b + 1)) hi x hr ⟨hmax, hx.2⟩
        exact ⟨ab, List.mem_cons_of_mem _ hin, h1, h2⟩

/-- `ivs` — the interval list of a list of proved classes. -/
def ivs {Q : Int → Prop} (cls : List (tpc Q)) : List (Int × Int) :=
  cls.map (fun c => (c.c_lo, c.c_hi))

theorem tp_dispatch : ∀ (Q : Int → Prop) (cls : List (tpc Q)) (lo hi : Int),
    tp_covers (ivs cls) lo hi = true → TPgen Q lo hi := by
  intro Q cls lo hi hc n hn
  obtain ⟨ab, hin, hab1, hab2⟩ := tp_covers_sound (ivs cls) lo hi n hc hn
  rw [ivs, List.mem_map] at hin
  obtain ⟨c, _, he⟩ := hin
  have h : c.c_lo ≤ n ∧ n ≤ c.c_hi := by
    rw [← he] at hab1 hab2
    exact ⟨hab1, hab2⟩
  exact c.c_ok n h

/-- Single class as a `TPgen` from a plain interval-quantified statement. -/
theorem tpgen_intro : ∀ (Q : Int → Prop) (lo hi : Int),
    (∀ n, lo ≤ n ∧ n ≤ hi → Q n) → TPgen Q lo hi :=
  fun _ _ _ H => H

theorem k_cases : ∀ k : Int, 1 ≤ k ∧ k ≤ 10 →
    k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by
  intro k hk
  omega

/-! ## Sanity checks (decidable checks) -/

example : tp_covers [(1, 5), (6, 10)] 1 10 = true := by decide
example : tp_covers [(1, 5), (7, 10)] 1 10 = false := by decide
example : tp_covers [] 3 2 = true := by decide

example : ivs [⟨1, 5, fun _ h => h.1⟩] = [(1, 5)] := by decide

end LinuxSem.Common.TargetCover
