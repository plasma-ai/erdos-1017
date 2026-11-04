module

public import Erdos1017.IntegerTransfer.ProfileMassBudget

/-!
# Cost budget for the rounding step

A fixed matching tolerance leaves room for the residual cost observable in the
same positive-probability selection, and the total matching inflation is small
for a tolerance chosen from the fixed clique-size cap and target error alone
(`matching_inflation_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

/-- A fixed matching tolerance leaves room for the residual cost observable
in the same positive-probability selection. -/
theorem normalized_residual_budget {B P Q τ ρ : ℝ}
    (hP : 0 ≤ P) (hPQ : P ≤ Q) (hQ : 0 < Q)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ) (hρτ : ρ ≤ τ / 16)
    (hB : B ≤ P + τ * Q / 16) :
    B / (P + τ * Q / 4) ≤ 1 - min ρ (1 / 2) := by
  have hden : 0 < P + τ * Q / 4 := by positivity
  have hθ : 0 ≤ min ρ (1 / 2) := le_min hρ.le (by norm_num)
  have hθτ : min ρ (1 / 2) ≤ τ / 16 := (min_le_left _ _).trans hρτ
  have hdenbound : P + τ * Q / 4 ≤ 5 * Q / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hτ1 hQ.le
    nlinarith only [hPQ, hmul]
  have hprod := mul_le_mul hθτ hdenbound hden.le (by positivity : (0 : ℝ) ≤ τ / 16)
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hB, hprod, mul_pos hτ hQ]

/-- The total matching inflation is small for a tolerance chosen using only
the fixed clique-size cap and target error. -/
theorem matching_inflation_le {R τ : ℝ} (hR : 0 ≤ R) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    let ρ := τ / (16 * (R + 1))
    (1 + ρ * R) * (1 + ρ) ≤ 1 + τ / 8 := by
  dsimp only
  have hden : 0 < 16 * (R + 1) := by positivity
  have hρ : 0 ≤ τ / (16 * (R + 1)) := div_nonneg hτ.le hden.le
  have hρ1 : τ / (16 * (R + 1)) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hidentity : τ / (16 * (R + 1)) * (R + 1) = τ / 16 := by field_simp
  have hprod := mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hρ hR)
  nlinarith only [hidentity, hprod, hρ]

end Erdos1017.MultipartiteAllocation
