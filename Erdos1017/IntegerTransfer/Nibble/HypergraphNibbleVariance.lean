module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibble

/-!
# Variance of the survivor count in one round

This module defines the number of vertices surviving one nibble round and proves
its expectation, a second-moment bound that assumes no independence between
survival events, an explicit variance bound from the degree and codegree
hypotheses, and a finite Chebyshev estimate (`survivorCount_deviation_mass`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual number of vertices surviving the deletion part of one nibble round. -/
def survivorCount (H : Finset (Finset V)) (X : Finset V → Bool) : ℝ :=
  ∑ v, untouched H X {v}

theorem survivorCount_eq_card (H : Finset (Finset V)) (X : Finset V → Bool) :
    survivorCount H X = ((Finset.univ.filter (fun v =>
      ∀ e ∈ incident H {v}, X e = false)).card : ℝ) := by
  simp only [survivorCount, untouched, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> norm_num

theorem survivorCount_expectation (H : Finset (Finset V)) (p : ℝ) :
    (∑ X, CliqueSampling.weight (fun _ => p) X * survivorCount H X) =
      ∑ v, (1 - p) ^ degree H v := by
  simp only [survivorCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [incident_singleton, degree] using untouched_expectation_const H p {v}

/-- A quantitative second-moment estimate for the actual number of surviving vertices.
No independence between the survival events is assumed. -/
theorem survivorCount_variance_le (H : Finset (Finset V)) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ X, CliqueSampling.weight (fun _ => p) X *
      (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2) ≤
      p * ∑ u : V, ∑ v : V, (codegree H u v : ℝ) := by
  have hmean (v : V) :
      (∑ X, CliqueSampling.weight (fun _ => p) X * untouched H X {v}) =
        (1 - p) ^ degree H v := by
    simpa only [incident_singleton, degree] using untouched_expectation_const H p {v}
  have hcov (u v : V) :
      (∑ X, CliqueSampling.weight (fun _ => p) X *
        ((untouched H X {u} - (1 - p) ^ degree H u) *
          (untouched H X {v} - (1 - p) ^ degree H v))) =
      (∑ X, CliqueSampling.weight (fun _ => p) X *
        (untouched H X {u} * untouched H X {v})) -
        (1 - p) ^ degree H u * (1 - p) ^ degree H v := by
    have hterm (X : Finset V → Bool) :
        CliqueSampling.weight (fun _ => p) X *
          ((untouched H X {u} - (1 - p) ^ degree H u) *
            (untouched H X {v} - (1 - p) ^ degree H v)) =
        CliqueSampling.weight (fun _ => p) X * (untouched H X {u} * untouched H X {v}) -
          (CliqueSampling.weight (fun _ => p) X * untouched H X {u}) * (1 - p) ^ degree H v -
          (CliqueSampling.weight (fun _ => p) X * untouched H X {v}) * (1 - p) ^ degree H u +
          CliqueSampling.weight (fun _ => p) X * ((1 - p) ^ degree H u * (1 - p) ^ degree H v) := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul, hmean, CliqueSampling.bernoulli_total, one_mul]
    ring
  have hexpand (X : Finset V → Bool) :
      (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 =
      ∑ u : V, ∑ v : V, (untouched H X {u} - (1 - p) ^ degree H u) *
        (untouched H X {v} - (1 - p) ^ degree H v) := by
    simp only [survivorCount, ← Finset.sum_sub_distrib, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  rw [hcov]
  exact survival_covariance_le H p hp hp1 u v

/-- The degree and codegree hypotheses of the matching theorem give an explicit variance bound. -/
theorem survivorCount_variance_le_degree_codegree (H : Finset (Finset V)) (p D c : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c)
    (hdegree : ∀ v, (degree H v : ℝ) ≤ D)
    (hcodegree : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ c) :
    (∑ X, CliqueSampling.weight (fun _ => p) X *
      (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2) ≤
      p * Fintype.card V * (D + Fintype.card V * c) := by
  have hpair (u v : V) : (codegree H u v : ℝ) ≤ (if v = u then D else 0) + c := by
    by_cases huv : u = v
    · subst v
      have heq : codegree H u u = degree H u := by simp [codegree, degree]
      simp only [↓reduceIte, heq]
      linarith [hdegree u]
    · simpa [Ne.symm huv] using hcodegree u v huv
  have hsum : (∑ u : V, ∑ v : V, (codegree H u v : ℝ)) ≤
      (Fintype.card V : ℝ) * (D + Fintype.card V * c) := by
    calc
      _ ≤ ∑ u : V, ∑ v : V, ((if v = u then D else 0) + c) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hpair u v))
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  have h := (survivorCount_variance_le H p hp hp1).trans (mul_le_mul_of_nonneg_left hsum hp)
  simpa only [mul_assoc] using h

/-- A finite Chebyshev estimate for the same actual sampling law. -/
theorem survivorCount_deviation_mass (H : Finset (Finset V)) (p t : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    t ^ 2 * (∑ X, if t ≤ |survivorCount H X - ∑ v, (1 - p) ^ degree H v| then
      CliqueSampling.weight (fun _ => p) X else 0) ≤
      p * ∑ u : V, ∑ v : V, (codegree H u v : ℝ) := by
  classical
  calc
    _ ≤ ∑ X, CliqueSampling.weight (fun _ => p) X *
        (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      have hw := CliqueSampling.weight_nonneg (fun _ : Finset V => p) (fun _ => ⟨hp, hp1⟩) X
      split_ifs with h
      · have hs : t ^ 2 ≤ (survivorCount H X - ∑ v, (1 - p) ^ degree H v) ^ 2 := by
          nlinarith [sq_abs (survivorCount H X - ∑ v, (1 - p) ^ degree H v)]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hs hw
      · simp only [mul_zero]
        exact mul_nonneg hw (sq_nonneg _)
    _ ≤ _ := survivorCount_variance_le H p hp hp1

end Erdos1017.HypergraphNibble
