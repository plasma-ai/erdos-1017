module

public import Erdos1017.IntegerTransfer.CliquePackingSampling
public import Mathlib.Data.Fintype.BigOperators

/-!
# Independent categorical labels on coordinates

This module defines the product law of independent labels on each coordinate, so
that allocations are mutually exclusive, and shows that each fixed label's
projection has the law of independent Bernoulli thinning with its marginal
probabilities (`projection_expectation`) and that distinct labels retain
disjoint coordinate sets.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CategoricalSampling

open scoped BigOperators

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

/-- Independent labels on each coordinate, allowing mutually exclusive allocations. -/
def weight (q : V → J → ℝ) (X : V → J) : ℝ := ∏ v, q v (X v)

/-- The Bernoulli projection recording one fixed allocation label. -/
abbrev projection (j : J) (X : V → J) (v : V) : Bool := decide (X v = j)

omit [DecidableEq J] in
theorem product_expectation (q : V → J → ℝ) (h : V → J → ℝ) :
    (∑ X, weight q X * ∏ v, h v (X v)) = ∏ v, ∑ a, q v a * h v a := by
  simp only [weight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun v a => q v a * h v a)).symm

omit [DecidableEq J] in
theorem total (q : V → J → ℝ) (hq : ∀ v, ∑ a, q v a = 1) :
    ∑ X, weight q X = 1 := by
  simpa only [mul_one, Finset.prod_const_one, hq] using product_expectation q (fun _ _ => 1)

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
theorem weight_nonneg (q : V → J → ℝ) (hq : ∀ v a, 0 ≤ q v a) (X : V → J) :
    0 ≤ weight q X := Finset.prod_nonneg (fun v _ => hq v (X v))

/-- The mass of each Boolean projection fibre is its exact product Bernoulli mass. -/
theorem projection_mass (q : V → J → ℝ) (hq : ∀ v, ∑ a, q v a = 1)
    (j : J) (B : V → Bool) :
    (∑ X, weight q X * if projection j X = B then (1 : ℝ) else 0) =
      CliqueSampling.weight (fun v => q v j) B := by
  classical
  have hprod (X : V → J) :
      (∏ v, if projection j X v = B v then (1 : ℝ) else 0) =
        if projection j X = B then 1 else 0 := by
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, forall_true_left, funext_iff]
  have hfactor (v : V) :
      (∑ a, q v a * if decide (a = j) = B v then (1 : ℝ) else 0) =
        if B v then q v j else 1 - q v j := by
    cases hB : B v
    · have hpoint (a : J) : q v a * (if decide (a = j) = false then (1 : ℝ) else 0) =
          q v a - if a = j then q v j else 0 := by
        by_cases h : a = j <;> simp [h]
      simp only [hpoint, Finset.sum_sub_distrib]
      simp [hq]
    · simp
  calc
    _ = ∑ X, weight q X * ∏ v, if projection j X v = B v then (1 : ℝ) else 0 := by
      simp only [hprod]
    _ = _ := by
      rw [product_expectation q (fun v a => if decide (a = j) = B v then 1 else 0)]
      simp only [hfactor, CliqueSampling.weight]

/-- Every observable of one allocation label has the same law as independent
Bernoulli thinning with its marginal probabilities. -/
theorem projection_expectation (q : V → J → ℝ) (hq : ∀ v, ∑ a, q v a = 1)
    (j : J) (f : (V → Bool) → ℝ) :
    (∑ X, weight q X * f (projection j X)) =
      ∑ B, CliqueSampling.weight (fun v => q v j) B * f B := by
  classical
  have hexpand (X : V → J) : f (projection j X) =
      ∑ B : V → Bool, (if projection j X = B then (1 : ℝ) else 0) * f B := by simp
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  simp only [← mul_assoc, ← Finset.sum_mul, projection_mass q hq]

omit [DecidableEq V] [Fintype J] in
/-- Distinct allocation labels always produce disjoint retained coordinate sets. -/
theorem projections_disjoint (X : V → J) {i j : J} (hij : i ≠ j) :
    Disjoint (Finset.univ.filter (fun v => projection i X v = true))
      (Finset.univ.filter (fun v => projection j X v = true)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hi : X v = i := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    projection, decide_eq_true_eq] using hi
  have hj : X v = j := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    projection, decide_eq_true_eq] using hj
  exact hij (hi.symm.trans hj)

end Erdos1017.CategoricalSampling
