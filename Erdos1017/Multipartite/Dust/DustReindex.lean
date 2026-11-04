module

public import Erdos1017.Multipartite.Dust.DustCellRestriction

/-!
# Relabeling heads of a dust dual

Symmetric finite duals and head duals can be relabeled arbitrarily, including
order reversal, without changing their pairs; head permutations preserve every
bounded all-count constraint, so the bounded homogeneous value is independent of
the order of head labels.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- Relabel a symmetric finite dual without changing the meaning of its pairs. -/
def reindexDual {m n : ℕ} (e : Fin m ≃ Fin n) (D : Selector.Dual n) : Selector.Dual m where
  alpha i := D.alpha (e i)
  beta i j := D.beta (e i) (e j)
  beta_symm i j := D.beta_symm (e i) (e j)
  beta_diag i := D.beta_diag (e i)

theorem reindexDual_objective {m n : ℕ} (e : Fin m ≃ Fin n) (D : Selector.Dual n)
    (p : Fin m → ℝ) :
    Selector.objective p (reindexDual e D) = Selector.objective (fun j => p (e.symm j)) D := by
  have hfirst : (∑ i, D.alpha (e i) * p i) = ∑ j, D.alpha j * p (e.symm j) := by
    simpa using e.sum_comp (fun j => D.alpha j * p (e.symm j))
  have hpair : (∑ i, ∑ j, D.beta (e i) (e j) * (p i * p j)) =
      ∑ i, ∑ j, D.beta i j * (p (e.symm i) * p (e.symm j)) := by
    have hrow (i : Fin m) : (∑ j, D.beta (e i) (e j) * (p i * p j)) =
        ∑ j, D.beta (e i) j * (p i * p (e.symm j)) := by
      simpa using e.sum_comp (fun j => D.beta (e i) j * (p i * p (e.symm j)))
    simp_rw [hrow]
    simpa using e.sum_comp (fun i => ∑ j, D.beta i j * (p (e.symm i) * p (e.symm j)))
  simp only [Selector.objective, reindexDual, hfirst, hpair]

/-- The symmetric head dual allows arbitrary relabeling, including order reversal. -/
def reindexHead {m n : ℕ} (e : Fin m ≃ Fin n) (C : Coefficients n) : Coefficients m
  | .inl i => head C (e i)
  | .inr (.inl (i, j)) => -(DustCellRestriction.headDual C).beta (e i) (e j)
  | .inr (.inr (.inl i)) => incident C (e i)
  | .inr (.inr (.inr false)) => linear C
  | .inr (.inr (.inr true)) => penalty C

theorem headDual_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (C : Coefficients n) :
    DustCellRestriction.headDual (reindexHead e C) = reindexDual e (DustCellRestriction.headDual C) := by
  have ha : (DustCellRestriction.headDual (reindexHead e C)).alpha =
      (reindexDual e (DustCellRestriction.headDual C)).alpha := rfl
  have hb : (DustCellRestriction.headDual (reindexHead e C)).beta =
      (reindexDual e (DustCellRestriction.headDual C)).beta := by
    funext i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [DustCellRestriction.headDual, reindexHead, reindexDual, pair, h]
    · simp [DustCellRestriction.headDual, reindexHead, reindexDual, pair]
    · change -(if i < j then -(DustCellRestriction.headDual C).beta (e i) (e j) else
        if j < i then -(DustCellRestriction.headDual C).beta (e j) (e i) else 0) =
        (DustCellRestriction.headDual C).beta (e i) (e j)
      simp [h, not_lt_of_gt h, Selector.Dual.beta_symm]
  cases hD : DustCellRestriction.headDual (reindexHead e C)
  cases hE : reindexDual e (DustCellRestriction.headDual C)
  simp only [hD, hE] at ha hb
  simp_all

/-- Separate the head-only part without changing any dust moments. -/
theorem objective_headDual {m : ℕ} (C : Coefficients m) (p : Fin m → ℝ) (s : ℝ) :
    objective p s C = Selector.objective p (DustCellRestriction.headDual C) + linear C * s -
      (∑ i, incident C i * p i * s) - penalty C * s ^ 2 / 2 := by
  rw [DustCellRestriction.headDual_objective]
  simp only [objective, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero,
    Finset.sum_const_zero, add_zero]
  ring

theorem reindexHead_objective {m n : ℕ} (e : Fin m ≃ Fin n) (C : Coefficients n)
    (p : Fin m → ℝ) (s : ℝ) :
    objective p s (reindexHead e C) = objective (fun j => p (e.symm j)) s C := by
  rw [objective_headDual, objective_headDual, headDual_reindex, reindexDual_objective]
  have hsum : (∑ i, incident C (e i) * p i * s) = ∑ j, incident C j * p (e.symm j) * s := by
    simpa using e.sum_comp (fun j => incident C j * p (e.symm j) * s)
  simpa only [incident, linear, penalty, reindexHead] using
    congrArg (fun z => Selector.objective (fun j => p (e.symm j)) (DustCellRestriction.headDual C) +
      linear C * s - z - penalty C * s ^ 2 / 2) hsum

/-- Arbitrary head permutations preserve every bounded all-count constraint. -/
theorem reindexHead_feasible {m n : ℕ} (e : Fin m ≃ Fin n) (C : Coefficients n)
    (hC : C ∈ feasible n) : reindexHead e C ∈ feasible m := by
  have hb (c : Coordinate n) : 0 ≤ C c ∧ C c ≤ 1 := ⟨hC.1.1 c, hC.1.2 c⟩
  have hbox (c : Coordinate m) : 0 ≤ reindexHead e C c ∧ reindexHead e C c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b))
    · exact hb _
    · simp only [reindexHead, DustCellRestriction.headDual, neg_neg]
      split_ifs <;> simp [pair, hb]
    · exact hb _
    · cases b <;> exact hb _
  refine ⟨⟨fun c => (hbox c).1, fun c => (hbox c).2⟩, ?_⟩
  intro X k
  rw [DustCellBridge.charge_eq_objective, reindexHead_objective]
  have h := hC.2 (fun j => X (e.symm j)) k
  rw [DustCellBridge.charge_eq_objective] at h
  exact h

/-- The bounded homogeneous value is independent of the order of its head labels. -/
theorem value_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (p : Fin m → ℝ) (s : ℝ) :
    value p s = value (fun j => p (e.symm j)) s := by
  obtain ⟨C, hC, heq⟩ := exists_value_eq p s
  obtain ⟨D, hD, heq'⟩ := exists_value_eq (fun j => p (e.symm j)) s
  apply le_antisymm
  · have h := le_csSup ((feasible_isCompact n).image
        (objective_continuous (fun j => p (e.symm j)) s)).bddAbove
      ⟨reindexHead e.symm C, reindexHead_feasible e.symm C hC, rfl⟩
    change objective (fun j => p (e.symm j)) s (reindexHead e.symm C) ≤
      value (fun j => p (e.symm j)) s at h
    simpa only [reindexHead_objective, Equiv.symm_symm, Equiv.symm_apply_apply, ← heq] using h
  · have h := le_csSup ((feasible_isCompact m).image (objective_continuous p s)).bddAbove
      ⟨reindexHead e D, reindexHead_feasible e D hD, rfl⟩
    change objective p s (reindexHead e D) ≤ value p s at h
    simpa only [reindexHead_objective, ← heq'] using h

end Erdos1017.MultipartiteDust
