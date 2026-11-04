module

public import Erdos1017.Multipartite.Selector.SelectorOptimalValue

/-!
# Clipping pair penalties of selector duals

Clipping a negative pair penalty to the incident linear charge keeps
feasibility, so the closed-cube selector optimum has a representative with every
pair penalty bounded by both incident linear charges (`exists_bounded_optimal`),
and every attained dual optimum has the exact selector value.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

/-- Change one unordered pair coefficient while preserving symmetry and zero diagonal. -/
def addPair {m : ℕ} (D : Dual m) (i j : Fin m) (hij : i ≠ j) (δ : ℝ) : Dual m where
  alpha := D.alpha
  beta k l := D.beta k l + (if k = i ∧ l = j then δ else 0) +
    (if k = j ∧ l = i then δ else 0)
  beta_symm k l := by rw [D.beta_symm]; simp only [and_comm]; ring
  beta_diag k := by
    have h₁ : ¬(k = i ∧ k = j) := fun h => hij (h.1.symm.trans h.2)
    have h₂ : ¬(k = j ∧ k = i) := fun h => hij (h.2.symm.trans h.1)
    simp [h₁, h₂, D.beta_diag]

theorem addPair_objective {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (i j : Fin m) (hij : i ≠ j) (δ : ℝ) :
    objective p (addPair D i j hij δ) = objective p D + δ * p i * p j := by
  unfold objective addPair
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- Clipping a negative pair penalty to the incident linear charge preserves
all Boolean inequalities. Other pair coefficients only decrease its exterior row. -/
theorem clipPair_feasible {m : ℕ} (D : Dual m) (hD : DualFeasible D)
    (hbeta : ∀ i j, D.beta i j ≤ 0) (i j : Fin m) (hij : i ≠ j) :
    DualFeasible (addPair D i j hij (-D.alpha i - D.beta i j)) := by
  intro X
  unfold quadratic
  rw [addPair_objective]
  by_cases hi : X i = true
  · by_cases hj : X j = true
    · have hdelete := hD (Function.update X i false)
      have hupdate : (fun k => bit (Function.update X i false k)) =
          Function.update (fun k => bit (X k)) i 0 := by
        funext k
        by_cases hk : k = i <;> simp [hk, bit, Function.update_of_ne]
      unfold quadratic at hdelete
      rw [hupdate, objective_update] at hdelete
      have hrow : (∑ k, D.beta i k * bit (X k)) ≤ D.beta i j := by
        have h : (∑ k, D.beta i k * bit (X k)) ≤
            ∑ k ∈ ({j} : Finset (Fin m)), D.beta i k * bit (X k) := by
          apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _)
          intro k _ _
          apply mul_nonpos_of_nonpos_of_nonneg (hbeta i k)
          cases X k <;> norm_num [bit]
        simpa [hj, bit] using h
      simp only [hi, hj, bit, ↓reduceIte] at *
      linarith
    · have hj' : X j = false := Bool.eq_false_iff.mpr hj
      simpa [hj', bit, quadratic] using hD X
  · have hi' : X i = false := Bool.eq_false_iff.mpr hi
    simpa [hi', bit, quadratic] using hD X

/-- At positive pair demand, any excessive penalty would strictly improve
under clipping, contradicting optimality. -/
theorem optimal_pair_lower_bound {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hD : DualOptimal p D)
    (halpha : ∀ i, 0 ≤ D.alpha i) (hbeta : ∀ i j, D.beta i j ≤ 0)
    (i j : Fin m) (hi : 0 < p i) (hj : 0 < p j) : -D.alpha i ≤ D.beta i j := by
  by_cases hij : i = j
  · subst j
    simpa [D.beta_diag] using neg_nonpos.mpr (halpha i)
  · have h := hD.2 (addPair D i j hij (-D.alpha i - D.beta i j))
      (clipPair_feasible D hD.1 hbeta i j hij)
    rw [addPair_objective] at h
    have hprod := mul_pos hi hj
    nlinarith

/-- Remove all zero-demand coordinates at once. -/
def removeZeros {m : ℕ} (p : Fin m → ℝ) (D : Dual m) : Dual m where
  alpha i := if p i = 0 then 0 else D.alpha i
  beta i j := if p i = 0 ∨ p j = 0 then 0 else D.beta i j
  beta_symm i j := by simp only [or_comm, D.beta_symm i j]
  beta_diag i := by simp [D.beta_diag]

theorem removeZeros_objective {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (q : Fin m → ℝ) :
    objective q (removeZeros p D) = objective (fun i => if p i = 0 then 0 else q i) D := by
  unfold objective removeZeros
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i = 0 <;> simp [hi]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : p i = 0 <;> by_cases hj : p j = 0 <;> simp [hi, hj]

theorem removeZeros_feasible {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hD : DualFeasible D) : DualFeasible (removeZeros p D) := by
  intro X
  unfold quadratic
  rw [removeZeros_objective]
  convert hD (fun i => if p i = 0 then false else X i) using 1
  unfold quadratic
  congr 1
  funext i
  by_cases hi : p i = 0 <;> simp [hi, bit]

theorem removeZeros_at_target {m : ℕ} (p : Fin m → ℝ) (D : Dual m) :
    objective p (removeZeros p D) = objective p D := by
  rw [removeZeros_objective]
  congr 1
  funext i
  split_ifs with hi
  · exact hi.symm
  · rfl

/-- The closed-cube selector optimum has a representative with every
pair penalty bounded by both incident linear charges, including zero demands. -/
theorem exists_bounded_optimal {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ∃ D : Dual m, DualOptimal p D ∧ (∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) ∧
      ∀ i j, -min (D.alpha i) (D.alpha j) ≤ D.beta i j ∧ D.beta i j ≤ 0 := by
  obtain ⟨w, hw, D, hD, heq, halpha, hbeta⟩ := exists_signed_primal_dual p hp
  refine ⟨removeZeros p D, ⟨removeZeros_feasible p D hD.1, ?_⟩, ?_, ?_⟩
  · intro E hE
    rw [removeZeros_at_target]
    exact hD.2 E hE
  · intro i
    by_cases hi : p i = 0 <;> simp [removeZeros, hi, halpha]
  · intro i j
    by_cases hi : p i = 0
    · simp only [removeZeros, hi, ↓reduceIte, true_or]
      have hjalpha : 0 ≤ if p j = 0 then 0 else D.alpha j := by
        split_ifs
        · exact le_rfl
        · exact (halpha j).1
      rw [min_eq_left hjalpha]
      norm_num
    · by_cases hj : p j = 0
      · simp only [removeZeros, hj, hi, ↓reduceIte, or_true]
        rw [min_eq_right (halpha i).1]
        norm_num
      · have hi' : 0 < p i := lt_of_le_of_ne (hp i).1 (Ne.symm hi)
        have hj' : 0 < p j := lt_of_le_of_ne (hp j).1 (Ne.symm hj)
        have h₁ := optimal_pair_lower_bound p D hD (fun k => (halpha k).1) hbeta i j hi' hj'
        have h₂ := optimal_pair_lower_bound p D hD (fun k => (halpha k).1) hbeta j i hj' hi'
        rw [D.beta_symm j i] at h₂
        simp only [removeZeros, hi, hj, ↓reduceIte, or_self]
        refine ⟨?_, hbeta i j⟩
        rcases le_total (D.alpha i) (D.alpha j) with h | h
        · simpa [min_eq_left h] using h₁
        · simpa [min_eq_right h] using h₂

/-- Every attained dual optimum has the exact selector infimum value. -/
theorem optimal_objective_eq_value {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (D : Dual m) (hD : DualOptimal p D) :
    objective p D = value p := by
  obtain ⟨w, hw, hwvalue, E, hE, hEvalue, hsigns⟩ := value_attained p hp
  rw [← hEvalue]
  exact le_antisymm (hE.2 D hD.1) (hD.2 E hE.1)

end Erdos1017.Selector
