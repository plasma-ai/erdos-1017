module

public import Erdos1017.Benchmark.SplitCurve

/-!
# Mass cap from the split count above a reciprocal cusp

The split count at a mass above a reciprocal cusp gives the normalized mass cap,
with no density-band or derivative assumption
(`splitValue_le_reciprocal_mass_cap`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Benchmark

/-- The actual split count at a mass above a reciprocal cusp gives the
normalized mass cap, without a density-band or derivative assumption. -/
theorem splitValue_le_reciprocal_mass_cap (k : ℕ) (hk : 2 ≤ k) {x : ℝ}
    (hx : 1 / (k : ℝ) ≤ x) : splitValue x ≤ (1 - 1 / (k : ℝ)) * x ^ 2 := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  let j := splitIndex x
  have hj : 1 ≤ j := le_max_left _ _
  have hj0 : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
  have hcount : j ≤ k - 1 := by
    apply max_le (by omega)
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    apply (div_le_iff₀ hx0).mpr
    have hp := (div_le_iff₀ hk0).mp hx
    nlinarith
  have hrecip : 1 / (k : ℝ) ≤ 1 / ((j : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show j + 1 ≤ k by omega)
  have he : (1 - 1 / ((j : ℝ) + 1)) * x ^ 2 - splitPolynomial j x =
      (((j : ℝ) + 1) * x - 1) ^ 2 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    unfold splitPolynomial
    field_simp
    ring
  have hpoly : splitPolynomial j x ≤ (1 - 1 / ((j : ℝ) + 1)) * x ^ 2 := by
    rw [← sub_nonneg, he]
    positivity
  have hvalue : splitValue x = splitPolynomial j x := by
    rw [splitValue, ite_eq_right hx0.ne']
    rfl
  rw [hvalue]
  exact hpoly.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg x))

end Erdos1017.Benchmark
