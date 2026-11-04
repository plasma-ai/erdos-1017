module

public import Erdos1017.IntegerTransfer.CliquePackingAccounting
public import Erdos1017.FractionalLimit.Selector

/-!
# Independent clique sampling

This module defines the product law of independent inclusion over a finite
clique family, with its exact moments.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueSampling

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Independent inclusion of every member of a finite clique family. -/
def weight (p : α → ℝ) (X : α → Bool) : ℝ :=
  ∏ i, if X i then p i else 1 - p i

/-- Product expectations factor, with no range assumption needed for the identity. -/
theorem bernoulli_product_expectation (p : α → ℝ)
    (h : α → Bool → ℝ) :
    (∑ X : α → Bool, weight p X * ∏ i, h i (X i)) =
      ∏ i, ((1 - p i) * h i false + p i * h i true) := by
  simp only [weight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if b then p i else 1 - p i) * h i b)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Every finite collection of distinct labels has its exact product moment. -/
theorem bernoulli_moment (p : α → ℝ) (S : Finset α) :
    (∑ X : α → Bool, weight p X * ∏ i ∈ S, Selector.bit (X i)) = ∏ i ∈ S, p i := by
  have h := bernoulli_product_expectation p (fun i b => if i ∈ S then Selector.bit b else 1)
  have hfactor : ∀ i : α,
      (1 - p i) * (if i ∈ S then Selector.bit false else 1) +
        p i * (if i ∈ S then Selector.bit true else 1) = if i ∈ S then p i else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi, Selector.bit]
  simp only [hfactor] at h
  simpa only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] using h

theorem bernoulli_total (p : α → ℝ) :
    ∑ X : α → Bool, weight p X = 1 := by
  simpa using bernoulli_moment p ∅

theorem bernoulli_first_moment (p : α → ℝ) (i : α) :
    (∑ X : α → Bool, weight p X * Selector.bit (X i)) = p i := by
  simpa using bernoulli_moment p {i}

theorem bernoulli_pair_moment (p : α → ℝ) (i j : α) (hij : i ≠ j) :
    (∑ X : α → Bool, weight p X * (Selector.bit (X i) * Selector.bit (X j))) = p i * p j := by
  simpa [hij] using bernoulli_moment p {i, j}

omit [DecidableEq α] in
theorem weight_nonneg (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (X : α → Bool) : 0 ≤ weight p X := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

end Erdos1017.CliqueSampling
