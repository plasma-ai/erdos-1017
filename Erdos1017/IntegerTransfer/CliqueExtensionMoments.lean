module

public import Erdos1017.IntegerTransfer.MultipartitePatternLift

/-!
# Extension counts and their first two moments

This module defines the number of extensions of a fixed base clique, expresses
its second moment as a count of two extensions sharing the base, and derives an
exceptional-base estimate from the first and second moments
(`exceptional_bases_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CliqueExtension

open scoped BigOperators

variable {B C : Type*} [Fintype C]

/-- The number of actual extensions of a fixed base. -/
def count (R : B → C → Prop) [DecidableRel R] (x : B) : ℝ :=
  ((Finset.univ.filter (R x)).card : ℝ)

/-- The extension count is its finite indicator sum. -/
theorem count_eq_sum (R : B → C → Prop) [DecidableRel R] (x : B) :
    count R x = ∑ y, if R x y then (1 : ℝ) else 0 := by
  simp only [count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- The second extension moment counts two independent extensions sharing the
same base, including coincident extensions. -/
theorem count_sq (R : B → C → Prop) [DecidableRel R] (x : B) :
    count R x ^ 2 = ∑ y, ∑ z, if R x y ∧ R x z then (1 : ℝ) else 0 := by
  rw [pow_two, count_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hy : R x y <;> by_cases hz : R x z <;> simp [hy, hz]

/-- Exact centered second moment on any specified family of base cliques. -/
theorem centered_moment (R : B → C → Prop) [DecidableRel R] (S : Finset B) (μ : ℝ) :
    (∑ x ∈ S, (count R x - μ) ^ 2) =
      (∑ x ∈ S, ∑ y, ∑ z, if R x y ∧ R x z then (1 : ℝ) else 0) -
        2 * μ * (∑ x ∈ S, count R x) + S.card * μ ^ 2 := by
  have hexpand : ∀ x, (count R x - μ) ^ 2 = count R x ^ 2 - 2 * μ * count R x + μ ^ 2 := by
    intro x
    ring
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, count_sq]

/-- Quantitative exceptional-base estimate from the actual first and second
extension moments, ready for the two concrete pattern-counting bounds. -/
theorem exceptional_bases_le (R : B → C → Prop) [DecidableRel R]
    (S : Finset B) (μ τ e₁ e₂ : ℝ) (hμ : 0 ≤ μ) (hτ : 0 ≤ τ)
    (hfirst : S.card * μ - e₁ ≤ ∑ x ∈ S, count R x)
    (hsecond : (∑ x ∈ S, ∑ y, ∑ z, if R x y ∧ R x z then (1 : ℝ) else 0) ≤
      S.card * μ ^ 2 + e₂) :
    τ ^ 2 * ((S.filter (fun x => τ ≤ |count R x - μ|)).card : ℝ) ≤ e₂ + 2 * μ * e₁ := by
  let T := S.filter (fun x => τ ≤ |count R x - μ|)
  have hbad : τ ^ 2 * (T.card : ℝ) ≤ ∑ x ∈ T, (count R x - μ) ^ 2 := by
    calc
      _ = ∑ _x ∈ T, τ ^ 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (by
        intro x hx
        have hx := (Finset.mem_filter.mp hx).2
        nlinarith [sq_abs (count R x - μ)])
  have hsubset : (∑ x ∈ T, (count R x - μ) ^ 2) ≤ ∑ x ∈ S, (count R x - μ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hcenter := centered_moment R S μ
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμ)
  change τ ^ 2 * (T.card : ℝ) ≤ _
  nlinarith

end Erdos1017.CliqueExtension
