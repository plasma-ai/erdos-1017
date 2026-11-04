module

public import Erdos1017.Multipartite.Dust.DustCellBridge

/-!
# Removing and inserting zero-mass heads

`removeHead` deletes one head and `insertHead` restores a head with zero
coefficients; both preserve the dust objective and feasibility, so zero-mass
heads have no effect on the bounded homogeneous optimum and appending finitely
many of them leaves the fixed-head value unchanged.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- Delete one head, retaining the order of all remaining head-pair coordinates. -/
def removeHead {m : ℕ} (i : Fin (m + 1)) (C : Coefficients (m + 1)) : Coefficients m
  | .inl j => head C (i.succAbove j)
  | .inr (.inl (j, k)) => pair C (i.succAbove j) (i.succAbove k)
  | .inr (.inr (.inl j)) => incident C (i.succAbove j)
  | .inr (.inr (.inr false)) => linear C
  | .inr (.inr (.inr true)) => penalty C

/-- Restore a head with zero coefficients, so it does not affect any count constraint. -/
def insertHead {m : ℕ} (i : Fin (m + 1)) (C : Coefficients m) : Coefficients (m + 1)
  | .inl j => (i.insertNth (0 : ℝ) (head C) : Fin (m + 1) → ℝ) j
  | .inr (.inl (j, k)) => (i.insertNth (fun _ : Fin (m + 1) => (0 : ℝ))
      (fun j => i.insertNth (0 : ℝ) (pair C j)) : Fin (m + 1) → Fin (m + 1) → ℝ) j k
  | .inr (.inr (.inl j)) => (i.insertNth (0 : ℝ) (incident C) : Fin (m + 1) → ℝ) j
  | .inr (.inr (.inr false)) => linear C
  | .inr (.inr (.inr true)) => penalty C

/-- Deleting a zero-mass head preserves the complete dust objective. -/
theorem removeHead_objective {m : ℕ} (i : Fin (m + 1)) (C : Coefficients (m + 1))
    (p : Fin m → ℝ) (s : ℝ) :
    objective p s (removeHead i C) = objective (i.insertNth 0 p) s C := by
  simp [objective, head, pair, incident, linear, penalty, removeHead,
    Fin.sum_univ_succAbove _ i, Fin.succAbove_lt_succAbove_iff]

/-- Extending the coefficients ignores the inserted mass coordinate. -/
theorem insertHead_objective {m : ℕ} (i : Fin (m + 1)) (C : Coefficients m)
    (p : Fin (m + 1) → ℝ) (s : ℝ) :
    objective p s (insertHead i C) = objective (i.removeNth p) s C := by
  simp [objective, head, pair, incident, linear, penalty, insertHead,
    Fin.sum_univ_succAbove _ i, Fin.succAbove_lt_succAbove_iff, Fin.removeNth]

/-- Restriction tests a head subset with the deleted head absent. -/
theorem removeHead_feasible {m : ℕ} (i : Fin (m + 1)) (C : Coefficients (m + 1))
    (hC : C ∈ feasible (m + 1)) : removeHead i C ∈ feasible m := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro c
    rcases c with j | (⟨j, k⟩ | (j | b))
    · exact hC.1.1 _
    · exact hC.1.1 _
    · exact hC.1.1 _
    · cases b <;> exact hC.1.1 _
  · intro c
    rcases c with j | (⟨j, k⟩ | (j | b))
    · exact hC.1.2 _
    · exact hC.1.2 _
    · exact hC.1.2 _
    · cases b <;> exact hC.1.2 _
  · intro X k
    have h := hC.2 (i.insertNth false X) k
    rw [DustCellBridge.charge_eq_objective] at h ⊢
    rw [removeHead_objective]
    have hbit : i.insertNth 0 (fun j => Selector.bit (X j)) =
        fun j => Selector.bit ((i.insertNth false X : Fin (m + 1) → Bool) j) := by
      funext j
      induction j using i.succAboveCases <;> simp [Selector.bit]
    simpa only [hbit, penalty, removeHead] using h

/-- An unused head can be inserted without weakening the all-count inequalities. -/
theorem insertHead_feasible {m : ℕ} (i : Fin (m + 1)) (C : Coefficients m)
    (hC : C ∈ feasible m) : insertHead i C ∈ feasible (m + 1) := by
  have hb (c : Coordinate m) : 0 ≤ C c ∧ C c ≤ 1 := ⟨hC.1.1 c, hC.1.2 c⟩
  have hbox (c : Coordinate (m + 1)) : 0 ≤ insertHead i C c ∧ insertHead i C c ≤ 1 := by
    rcases c with j | (⟨j, k⟩ | (j | b))
    · induction j using i.succAboveCases <;> simp [insertHead, head, hb]
    · induction j using i.succAboveCases <;> induction k using i.succAboveCases <;>
        simp [insertHead, pair, hb]
    · induction j using i.succAboveCases <;> simp [insertHead, incident, hb]
    · cases b <;> exact hb _
  refine ⟨⟨fun c => (hbox c).1, fun c => (hbox c).2⟩, ?_⟩
  intro X k
  rw [DustCellBridge.charge_eq_objective, insertHead_objective]
  have h := hC.2 (i.removeNth X) k
  rw [DustCellBridge.charge_eq_objective] at h
  exact h

/-- Zero-mass heads have no effect on the bounded homogeneous optimum. -/
theorem value_insert_zero {m : ℕ} (i : Fin (m + 1)) (p : Fin m → ℝ) (s : ℝ) :
    value (i.insertNth 0 p) s = value p s := by
  obtain ⟨C, hC, heq⟩ := exists_value_eq (i.insertNth 0 p) s
  obtain ⟨D, hD, heq'⟩ := exists_value_eq p s
  apply le_antisymm
  · rw [heq, ← removeHead_objective]
    exact le_csSup ((feasible_isCompact m).image (objective_continuous p s)).bddAbove
      ⟨removeHead i C, removeHead_feasible i C hC, rfl⟩
  · have h := le_csSup ((feasible_isCompact (m + 1)).image
        (objective_continuous (i.insertNth 0 p) s)).bddAbove
      ⟨insertHead i D, insertHead_feasible i D hD, rfl⟩
    change objective (i.insertNth 0 p) s (insertHead i D) ≤ value (i.insertNth 0 p) s at h
    simpa only [insertHead_objective, Fin.removeNth_insertNth, ← heq'] using h

/-- Appending any finite number of zero-mass heads leaves the same fixed-head value. -/
theorem value_append_zero {m : ℕ} (p : Fin m → ℝ) (s : ℝ) (n : ℕ) :
    value (Fin.append p (fun _ : Fin n => 0)) s = value p s := by
  induction n with
  | zero =>
    have hp : Fin.append p (fun _ : Fin 0 => (0 : ℝ)) = p := by
      funext i
      simp only [Fin.append, Fin.addCases]
      split_ifs with hi
      · exact congrArg p (Fin.ext rfl)
      · exact (hi i.isLt).elim
    rw [hp]
  | succ n ih =>
    have hz : (fun _ : Fin (n + 1) => (0 : ℝ)) = Fin.snoc (fun _ : Fin n => 0) 0 := by
      funext i
      induction i using Fin.lastCases <;> simp
    rw [hz, Fin.append_snoc, ← Fin.insertNth_last', value_insert_zero, ih]

end Erdos1017.MultipartiteDust
