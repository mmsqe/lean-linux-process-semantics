/-
  * Common.SharedFacts — the generic facts that more than one layer needs.

  NOT A TRUST BOUNDARY: no statement in this file is part of the trusted
  specification.  It is the shared home for lemmas that describe a definition
  in `LinuxProcessSem` (the monad, the state, the run, an ABI helper) and that
  were being restated privately, file by file, wherever a proof needed them.
  The policy is the same one `RocqSpelling.lean` applies to the port's
  spellings: state the fact once, here or in the module that owns the
  definition, and delete the copies.

  WHY THIS MODULE CAN HOLD THEM.  It sits above `Run` and `State`, so every
  lemma about an input projection (`in_arg`, `in_sysno`), a monad law instance
  (`bind_ok_iff`, `bind_unmodeled_iff`, `seqSpec_…`), a byte-vector helper, or
  an ABI arithmetic fact can be stated here and imported from anywhere that
  already sees `Run`.  A module BELOW `Run` (e.g. `State`, `RiscvSemantics`)
  cannot import this one; a fact needed there belongs in that module, not
  here.  A fact that names a `Checks`-layer definition (`check_ret_only`,
  `check_result`) cannot live here either — `Checks` is above `Common`; those
  live in `Checks/Sys/Prelude.lean`.

  Every entry states the SAME claim its deleted copies stated; the copies were
  statement-identical (checked before deletion), so deleting them changed no
  proof, only where the name resolves.
-/
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.Sys.Syscall

namespace LinuxSem.Common.SharedFacts

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Sys.Syscall (record_copyins ret_only err_ret errno_from)

/- The facts below were each restated privately in several modules; those
   copies are gone and every caller now resolves the name here. -/

/-- An instruction that touches no memory materializes nothing: the
    accounting layer is the identity on the model, WHATEVER the lazy
    ledger holds.  This is `State.materialize_model_accesses_no_lazy`'s
    dual, and it is what frees the loop lemmas from any `m_vm_lazy`
    hypothesis — the ASan spin runs long after MAP_NORESERVE mappings
    have populated the lazy ledger. -/
theorem materialize_model_accesses_nil (m : Model) :
    materialize_model_accesses m [] = some m := by
  obtain ⟨fd, vm, io, fs, proc, lim, time⟩ := m
  obtain ⟨maps, lazy, mat⟩ := vm
  rfl

/-- `record_copyins reads (ret_only r)`: the answer `r`, no writes, and
    `reads` on the copy-in ledger.  (`record_copyins` prepends to
    `eff.eff_copyins`, which is `[]` for `ret_only`, so the
    `reads ++ []` it builds is that same list.) -/
theorem record_copyins_ret_only_ok (reads : List (word × Nat))
    (r : word) (i : SyscallInput) (m : Model) :
    record_copyins reads (ret_only r) i m
      (.ok (with_copyins reads (mkEffect r [] [])) m []) := by
  refine ⟨mkEffect r [] [], m, [], [], rfl, ?_, rfl⟩
  simp [LinuxSem.LinuxProcessSem.pure, with_copyins, List.append_nil]


theorem is_prefix_app_mono {A : Type} (l a b : List A)
    (H : is_prefix a b) : is_prefix (l ++ a) (l ++ b) := by
  induction l with
  | nil => exact H
  | cons x l ih => exact ⟨rfl, ih⟩


theorem is_prefix_app_r {A : Type} (l m a : List A)
    (H : is_prefix a l) : is_prefix a (l ++ m) := by
  induction l generalizing a with
  | nil =>
    cases a with
    | nil => exact is_prefix_nil _
    | cons _ _ => exact False.elim H
  | cons x l ih =>
    cases a with
    | nil => exact is_prefix_nil _
    | cons y a =>
      obtain ⟨rfl, H'⟩ := H
      exact ⟨rfl, ih a H'⟩


/-- `LazyFrame:137`.  A page inserted into a list is the inserted page
    or was already there. -/
theorem page_insert_in (p q : word) (pages : List word)
    (h : p ∈ page_insert q pages) : p = q ∨ p ∈ pages := by
  unfold page_insert at h
  split at h
  · exact Or.inr h
  · rcases List.mem_cons.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'


/-- `LazyFrame:147`.  Every page the cursor inserts is the page of some
    byte offset [k < n] past [base] (in unwrapped [Z], matching the
    cursor). -/
theorem access_pages_acc_in (base : Int) (n : Nat) (pages : List word) (p : word)
    (h : p ∈ access_pages_acc base n pages) :
    p ∈ pages ∨ ∃ k, k < n ∧ p = page_base_of (base + (k : Int)) := by
  induction n generalizing base pages with
  | zero => exact Or.inl (by simpa [access_pages_acc] using h)
  | succ k ih =>
    simp only [access_pages_acc] at h
    rcases ih (base + 1) _ h with hin | ⟨j, hj, hp⟩
    · rcases page_insert_in _ _ _ hin with heq | hin
      · subst heq
        exact Or.inr ⟨0, by omega, by simp⟩
      · exact Or.inl hin
    · refine Or.inr ⟨j + 1, by omega, ?_⟩
      rw [hp]
      congr 1
      omega


/-- `LazyFrame:161`.  Every page an access report can name is either
    already in the list or is the page of some byte [k < n] past one of
    the report's accesses. -/
theorem accesses_pages_in (accs : List (word × Nat)) (pages : List word) (p : word)
    (h : p ∈ accesses_pages accs pages) :
    p ∈ pages ∨ ∃ a n k, (a, n) ∈ accs ∧ k < n
      ∧ p = page_base_of ((a.toNat : Int) + (k : Int)) := by
  induction accs generalizing pages with
  | nil => exact Or.inl (by simpa [accesses_pages] using h)
  | cons x accs ih =>
    obtain ⟨aw, n⟩ := x
    simp only [accesses_pages] at h
    rcases ih _ h with hin | ⟨a', n', k, hin', hk, hp⟩
    · rcases access_pages_acc_in (aw.toNat : Int) n pages p hin with hp' | ⟨k, hk, hp'⟩
      · exact Or.inl hp'
      · exact Or.inr ⟨aw, n, k, List.mem_cons_self, hk, hp'⟩
    · exact Or.inr ⟨a', n', k, List.mem_cons_of_mem _ hin', hk, hp⟩

end LinuxSem.Common.SharedFacts
