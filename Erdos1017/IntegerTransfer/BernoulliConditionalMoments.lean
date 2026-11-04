module

public import Erdos1017.IntegerTransfer.BernoulliFamily

/-!
# Moments conditional on a retained base

A base-retention event is independent of each extension support disjoint from
it, so it factors out of the first and second moments, and conditioning on it
leaves the degree variance unchanged up to the exact retention probability
(`base_variance`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.BernoulliFamily

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- A base-retention event is independent of each extension support disjoint from it. -/
theorem base_first_moment (F : Finset I) (S : I → Finset V) (B : Finset V) (p : V → ℝ)
    (hdisj : ∀ i ∈ F, Disjoint B (S i)) :
    (∑ X, CliqueSampling.weight p X *
      (BernoulliPresence.present X B * ((retained F S X).card : ℝ))) =
      (∏ v ∈ B, p v) * mean F S p := by
  simp only [retained_card, Finset.mul_sum, mean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [BernoulliPresence.present_mul]
  rw [BernoulliPresence.expectation, Finset.prod_union (hdisj i hi)]

/-- The same independent base event factors out of the actual second moment. -/
theorem base_second_moment (F : Finset I) (S : I → Finset V) (B : Finset V) (p : V → ℝ)
    (hdisj : ∀ i ∈ F, Disjoint B (S i)) :
    (∑ X, CliqueSampling.weight p X *
      (BernoulliPresence.present X B * ((retained F S X).card : ℝ) ^ 2)) =
      (∏ v ∈ B, p v) *
        (∑ X, CliqueSampling.weight p X * ((retained F S X).card : ℝ) ^ 2) := by
  have hsquare (X : V → Bool) : ((retained F S X).card : ℝ) ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, BernoulliPresence.present X (S i) * BernoulliPresence.present X (S j) := by
    rw [retained_card, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  simp only [hsquare, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  have hdisj' := Finset.disjoint_union_right.mpr ⟨hdisj i hi, hdisj j hj⟩
  simp_rw [BernoulliPresence.present_mul]
  rw [BernoulliPresence.expectation, BernoulliPresence.expectation, Finset.prod_union hdisj']

/-- Conditioning on an independently retained base does not change the degree
variance; its probability is retained as an exact multiplicative factor. -/
theorem base_variance (F : Finset I) (S : I → Finset V) (B : Finset V) (p : V → ℝ)
    (hdisj : ∀ i ∈ F, Disjoint B (S i)) :
    (∑ X, CliqueSampling.weight p X *
      (BernoulliPresence.present X B * (((retained F S X).card : ℝ) - mean F S p) ^ 2)) =
      (∏ v ∈ B, p v) *
        (∑ X, CliqueSampling.weight p X * (((retained F S X).card : ℝ) - mean F S p) ^ 2) := by
  have hpoly (X : V → Bool) :
      CliqueSampling.weight p X *
        (BernoulliPresence.present X B * (((retained F S X).card : ℝ) - mean F S p) ^ 2) =
      CliqueSampling.weight p X * (BernoulliPresence.present X B * ((retained F S X).card : ℝ) ^ 2) -
        2 * mean F S p * (CliqueSampling.weight p X *
          (BernoulliPresence.present X B * ((retained F S X).card : ℝ))) +
        (mean F S p) ^ 2 * (CliqueSampling.weight p X * BernoulliPresence.present X B) := by ring
  have hpoly' (X : V → Bool) :
      CliqueSampling.weight p X * (((retained F S X).card : ℝ) - mean F S p) ^ 2 =
      CliqueSampling.weight p X * ((retained F S X).card : ℝ) ^ 2 -
        2 * mean F S p * (CliqueSampling.weight p X * ((retained F S X).card : ℝ)) +
        (mean F S p) ^ 2 * CliqueSampling.weight p X := by ring
  simp_rw [hpoly, hpoly']
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    base_first_moment F S B p hdisj, base_second_moment F S B p hdisj,
    BernoulliPresence.expectation, expectation, CliqueSampling.bernoulli_total]
  ring

end Erdos1017.BernoulliFamily
