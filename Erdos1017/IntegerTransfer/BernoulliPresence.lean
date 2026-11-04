module

public import Erdos1017.IntegerTransfer.CliquePackingSampling

/-!
# Presence indicators under independent thinning

This module defines the indicator `present` that every coordinate of a finite
set is retained, with its exact product mean under nonuniform independent
thinning, zero covariance for disjoint sets, and covariance bounded by the
overlap size (`covariance_le_inter`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.BernoulliPresence

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Indicator that every coordinate in the finite set is retained. -/
def present (X : V → Bool) (S : Finset V) : ℝ := if ∀ v ∈ S, X v = true then 1 else 0

theorem present_eq_prod (X : V → Bool) (S : Finset V) :
    present X S = ∏ v ∈ S, Selector.bit (X v) := by
  simp only [Selector.bit, Finset.prod_boole, present]
  by_cases h : ∀ v ∈ S, X v = true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

theorem present_mul (X : V → Bool) (S T : Finset V) :
    present X S * present X T = present X (S ∪ T) := by
  have hu : (∀ v ∈ S ∪ T, X v = true) ↔ (∀ v ∈ S, X v = true) ∧ ∀ v ∈ T, X v = true := by
    simp only [Finset.mem_union, or_imp, forall_and]
  by_cases hs : ∀ v ∈ S, X v = true
  · by_cases ht : ∀ v ∈ T, X v = true
    · simp only [present, ite_eq_left hs, ite_eq_left ht, ite_eq_left (hu.mpr ⟨hs, ht⟩), one_mul]
    · have hn := fun h => ht (hu.mp h).2
      simp only [present, ite_eq_left hs, ite_eq_right ht, ite_eq_right hn, mul_zero]
  · have hn := fun h => hs (hu.mp h).1
    simp only [present, ite_eq_right hs, ite_eq_right hn, zero_mul]

/-- Nonuniform independent vertex thinning has the exact product mean. -/
theorem expectation (p : V → ℝ) (S : Finset V) :
    (∑ X, CliqueSampling.weight p X * present X S) = ∏ v ∈ S, p v := by
  simp_rw [present_eq_prod]
  exact CliqueSampling.bernoulli_moment p S

/-- Disjoint coordinate sets give independent retention events. -/
theorem covariance_eq_zero (p : V → ℝ) (S T : Finset V) (h : Disjoint S T) :
    (∑ X, CliqueSampling.weight p X * (present X S * present X T)) -
      (∏ v ∈ S, p v) * (∏ v ∈ T, p v) = 0 := by
  simp_rw [present_mul]
  rw [expectation, Finset.prod_union h, sub_self]

/-- The overlap size bounds covariance, uniformly over all vertex probabilities. -/
theorem covariance_le_inter (p : V → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (S T : Finset V) :
    (∑ X, CliqueSampling.weight p X * (present X S * present X T)) -
      (∏ v ∈ S, p v) * (∏ v ∈ T, p v) ≤ (S ∩ T).card := by
  by_cases h : Disjoint S T
  · rw [covariance_eq_zero p S T h]
    positivity
  · have hc : 0 < (S ∩ T).card :=
      Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp h)
    have hc' : (1 : ℝ) ≤ (S ∩ T).card := by exact_mod_cast hc
    have hprod : (∏ v ∈ S ∪ T, p v) ≤ 1 :=
      Finset.prod_le_one₀ (fun v _ => (hp v).1) (fun v _ => (hp v).2)
    have hnonneg : 0 ≤ (∏ v ∈ S, p v) * (∏ v ∈ T, p v) :=
      mul_nonneg (Finset.prod_nonneg (fun v _ => (hp v).1))
        (Finset.prod_nonneg (fun v _ => (hp v).1))
    simp_rw [present_mul]
    rw [expectation]
    linarith

end Erdos1017.BernoulliPresence
