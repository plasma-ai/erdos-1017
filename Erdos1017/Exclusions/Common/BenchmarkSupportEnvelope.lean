module

public import Erdos1017.Benchmark.SplitCurve

/-!
# Support constant from the split curve

The split curve gives the sharp support constant
(`splitValue_sub_half_square_le`), with a proof by its integer index that covers
the zero and unit endpoints.
-/

@[expose] public section

namespace Erdos1017.Benchmark

private theorem support_index_polynomial_nonneg (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ (j : ℝ) ^ 3 + 6 * (j : ℝ) ^ 2 - 41 * (j : ℝ) + 50 := by
  rcases eq_or_lt_of_le hj with rfl | hj
  · norm_num
  by_cases htwo : j = 2
  · subst j
    norm_num
  have hthree : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
  have hid : (j : ℝ) ^ 3 + 6 * (j : ℝ) ^ 2 - 41 * (j : ℝ) + 50 =
      ((j : ℝ) - 3) ^ 3 + 15 * ((j : ℝ) - 3) ^ 2 + 22 * ((j : ℝ) - 3) + 8 := by
    ring
  rw [hid]
  have ht : 0 ≤ (j : ℝ) - 3 := sub_nonneg.mpr hthree
  positivity

private theorem splitPolynomial_sub_half_square_le (j : ℕ) (hj : 1 ≤ j) (a : ℝ) :
    splitPolynomial j a - a ^ 2 / 2 ≤ 1 / 48 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  let D : ℝ := (j : ℝ) * ((j : ℝ) + 1)
  let C : ℝ := (j : ℝ) ^ 2 + 5 * (j : ℝ) + 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hid : 48 * D * C * (1 / 48 - splitPolynomial j a + a ^ 2 / 2) =
      24 * (C * a - 2 * ((j : ℝ) + 1)) ^ 2 +
        (j : ℝ) * ((j : ℝ) ^ 3 + 6 * (j : ℝ) ^ 2 - 41 * (j : ℝ) + 50) := by
    dsimp [D, C]
    unfold splitPolynomial
    field_simp
    ring
  have hnonneg : 0 ≤ 48 * D * C * (1 / 48 - splitPolynomial j a + a ^ 2 / 2) := by
    rw [hid]
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg hj0.le (support_index_polynomial_nonneg j hj))
  have h := (mul_nonneg_iff_of_pos_left (by positivity : 0 < 48 * D * C)).mp hnonneg
  linarith

/-- The actual split curve gives the sharp support constant. The proof
uses its actual integer index, including the zero and unit endpoints. -/
theorem splitValue_sub_half_square_le {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    splitValue a - a ^ 2 / 2 ≤ 1 / 48 := by
  by_cases hzero : a = 0
  · subst a
    norm_num [splitValue]
  have hindex : 1 ≤ splitIndex a := le_max_left _ _
  have hvalue : splitValue a = splitPolynomial (splitIndex a) a := by
    simp only [splitValue, hzero, ↓reduceIte, splitPolynomial]
  rw [hvalue]
  exact splitPolynomial_sub_half_square_le (splitIndex a) hindex a

end Erdos1017.Benchmark
