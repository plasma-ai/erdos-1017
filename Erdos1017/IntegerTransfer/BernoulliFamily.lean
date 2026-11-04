module

public import Erdos1017.IntegerTransfer.BernoulliPresence

/-!
# Retained members of a family under independent thinning

This module defines the retained members of a finite family under independent
coordinate thinning and their exact mean, bounds the variance by the number of
overlapping supports (`variance_le`), and derives a finite Chebyshev estimate
(`deviation_mass`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.BernoulliFamily

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- Actual members of a finite family whose required coordinates are all retained. -/
def retained (F : Finset I) (S : I → Finset V) (X : V → Bool) : Finset I :=
  F.filter (fun i => ∀ v ∈ S i, X v = true)

/-- The exact expected size of a family under independent coordinate thinning. -/
def mean (F : Finset I) (S : I → Finset V) (p : V → ℝ) : ℝ :=
  ∑ i ∈ F, ∏ v ∈ S i, p v

theorem retained_card (F : Finset I) (S : I → Finset V) (X : V → Bool) :
    ((retained F S X).card : ℝ) = ∑ i ∈ F, BernoulliPresence.present X (S i) := by
  simp only [retained, BernoulliPresence.present, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

theorem expectation (F : Finset I) (S : I → Finset V) (p : V → ℝ) :
    (∑ X, CliqueSampling.weight p X * ((retained F S X).card : ℝ)) = mean F S p := by
  simp only [retained_card, Finset.mul_sum, mean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact BernoulliPresence.expectation p (S i)

/-- Only intersecting supports contribute to the variance. Each covariance is at most one. -/
theorem variance_le_overlaps (F : Finset I) (S : I → Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) :
    (∑ X, CliqueSampling.weight p X * (((retained F S X).card : ℝ) - mean F S p) ^ 2) ≤
      ∑ i ∈ F, ((F.filter (fun j => ¬Disjoint (S i) (S j))).card : ℝ) := by
  have hmean (i : I) := BernoulliPresence.expectation p (S i)
  have hcov (i j : I) :
      (∑ X, CliqueSampling.weight p X *
        ((BernoulliPresence.present X (S i) - ∏ v ∈ S i, p v) *
          (BernoulliPresence.present X (S j) - ∏ v ∈ S j, p v))) =
      (∑ X, CliqueSampling.weight p X *
        (BernoulliPresence.present X (S i) * BernoulliPresence.present X (S j))) -
        (∏ v ∈ S i, p v) * (∏ v ∈ S j, p v) := by
    have hterm (X : V → Bool) :
        CliqueSampling.weight p X *
          ((BernoulliPresence.present X (S i) - ∏ v ∈ S i, p v) *
            (BernoulliPresence.present X (S j) - ∏ v ∈ S j, p v)) =
        CliqueSampling.weight p X * (BernoulliPresence.present X (S i) *
          BernoulliPresence.present X (S j)) -
          (CliqueSampling.weight p X * BernoulliPresence.present X (S i)) * (∏ v ∈ S j, p v) -
          (CliqueSampling.weight p X * BernoulliPresence.present X (S j)) * (∏ v ∈ S i, p v) +
          CliqueSampling.weight p X * ((∏ v ∈ S i, p v) * (∏ v ∈ S j, p v)) := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul, hmean, CliqueSampling.bernoulli_total, one_mul]
    ring
  have hexpand (X : V → Bool) :
      (((retained F S X).card : ℝ) - mean F S p) ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, (BernoulliPresence.present X (S i) - ∏ v ∈ S i, p v) *
        (BernoulliPresence.present X (S j) - ∏ v ∈ S j, p v) := by
    simp only [retained_card, mean, ← Finset.sum_sub_distrib, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_comm]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j _
  rw [hcov]
  by_cases h : Disjoint (S i) (S j)
  · rw [BernoulliPresence.covariance_eq_zero p (S i) (S j) h]
    simp [h]
  · simp only [h, not_false_eq_true, ↓reduceIte, Nat.cast_one]
    simp_rw [BernoulliPresence.present_mul]
    rw [BernoulliPresence.expectation]
    have hprod : (∏ v ∈ S i ∪ S j, p v) ≤ 1 :=
      Finset.prod_le_one₀ (fun v _ => (hp v).1) (fun v _ => (hp v).2)
    have hnonneg : 0 ≤ (∏ v ∈ S i, p v) * (∏ v ∈ S j, p v) :=
      mul_nonneg (Finset.prod_nonneg (fun v _ => (hp v).1))
        (Finset.prod_nonneg (fun v _ => (hp v).1))
    linarith

/-- A uniform bound on the number of overlapping supports bounds the variance. -/
theorem variance_le (F : Finset I) (S : I → Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (B : ℝ)
    (hB : ∀ i ∈ F, ((F.filter (fun j => ¬Disjoint (S i) (S j))).card : ℝ) ≤ B) :
    (∑ X, CliqueSampling.weight p X * (((retained F S X).card : ℝ) - mean F S p) ^ 2) ≤
      F.card * B := by
  calc
    _ ≤ ∑ i ∈ F, ((F.filter (fun j => ¬Disjoint (S i) (S j))).card : ℝ) :=
      variance_le_overlaps F S p hp
    _ ≤ ∑ _ ∈ F, B := Finset.sum_le_sum hB
    _ = _ := by simp

/-- Finite Chebyshev for the actual number of retained family members. -/
theorem deviation_mass (F : Finset I) (S : I → Finset V) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (B t : ℝ) (ht : 0 ≤ t)
    (hB : ∀ i ∈ F, ((F.filter (fun j => ¬Disjoint (S i) (S j))).card : ℝ) ≤ B) :
    t ^ 2 * (∑ X, if t ≤ |((retained F S X).card : ℝ) - mean F S p| then
      CliqueSampling.weight p X else 0) ≤ F.card * B := by
  classical
  calc
    _ ≤ ∑ X, CliqueSampling.weight p X * (((retained F S X).card : ℝ) - mean F S p) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X _
      have hw := CliqueSampling.weight_nonneg p hp X
      split_ifs with h
      · have hs : t ^ 2 ≤ (((retained F S X).card : ℝ) - mean F S p) ^ 2 := by
          nlinarith [sq_abs (((retained F S X).card : ℝ) - mean F S p)]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hs hw
      · simp only [mul_zero]
        exact mul_nonneg hw (sq_nonneg _)
    _ ≤ _ := variance_le F S p hp B hB

end Erdos1017.BernoulliFamily
