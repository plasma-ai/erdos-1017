module

public import Erdos1017.IntegerTransfer.CliquePackingSampling
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Rectangle discrepancy for weights in the unit interval

Weighted bilinear sums are averages of indicator rectangles selected by Boolean
endpoint weights, so a uniform rectangle discrepancy bound also controls all
weights in `[0,1]`.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedRectangle

open scoped BigOperators

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
/-- Boolean endpoint weights select an actual rectangle. -/
theorem indicator_sum_eq (X : A → Bool) (Y : B → Bool) (K : A → B → ℝ) :
    (∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * K a b) =
      ∑ a ∈ Finset.univ.filter (fun a => X a = true),
        ∑ b ∈ Finset.univ.filter (fun b => Y b = true), K a b := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  cases hX : X a
  · simp [Selector.bit]
  · simp only [Selector.bit, ↓reduceIte, one_mul]
    apply Finset.sum_congr rfl
    intro b _
    cases Y b <;> simp

/-- Weighted bilinear sums are averages of the corresponding indicator rectangles. -/
theorem bernoulli_representation (p : A → ℝ) (q : B → ℝ) (K : A → B → ℝ) :
    (∑ X : A → Bool, ∑ Y : B → Bool,
      CliqueSampling.weight p X * CliqueSampling.weight q Y *
        ∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * K a b) =
      ∑ a, ∑ b, p a * q b * K a b := by
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (B → Bool)))
    (t := (Finset.univ : Finset A))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (A → Bool)))
    (t := (Finset.univ : Finset A))]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (B → Bool)))
    (t := (Finset.univ : Finset B))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (A → Bool)))
    (t := (Finset.univ : Finset B))]
  apply Finset.sum_congr rfl
  intro b _
  have hfactor (X : A → Bool) (Y : B → Bool) :
      CliqueSampling.weight p X * CliqueSampling.weight q Y *
        (Selector.bit (X a) * Selector.bit (Y b) * K a b) =
      (CliqueSampling.weight p X * Selector.bit (X a)) *
        (CliqueSampling.weight q Y * Selector.bit (Y b)) * K a b := by ring
  simp_rw [hfactor, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [CliqueSampling.bernoulli_first_moment, ← Finset.sum_mul,
    CliqueSampling.bernoulli_first_moment]

/-- A uniform rectangle discrepancy bound also controls all weights in `[0,1]`.
The proof averages actual independently selected rectangles. -/
theorem abs_sum_le (K : A → B → ℝ) (η : ℝ)
    (hK : ∀ (X : A → Bool) (Y : B → Bool),
      |∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * K a b| ≤ η)
    (p : A → ℝ) (q : B → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (hq : ∀ b, 0 ≤ q b ∧ q b ≤ 1) :
    |∑ a, ∑ b, p a * q b * K a b| ≤ η := by
  rw [← bernoulli_representation p q K]
  calc
    _ ≤ ∑ X : A → Bool, ∑ Y : B → Bool,
        |CliqueSampling.weight p X * CliqueSampling.weight q Y *
          ∑ a, ∑ b, Selector.bit (X a) * Selector.bit (Y b) * K a b| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun X _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ X : A → Bool, ∑ Y : B → Bool,
        CliqueSampling.weight p X * CliqueSampling.weight q Y * η := by
      apply Finset.sum_le_sum
      intro X _
      apply Finset.sum_le_sum
      intro Y _
      have hw := mul_nonneg (CliqueSampling.weight_nonneg p hp X)
        (CliqueSampling.weight_nonneg q hq Y)
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hK X Y) hw
    _ = η := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, CliqueSampling.bernoulli_total, one_mul]

end Erdos1017.WeightedRectangle
