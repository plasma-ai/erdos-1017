module

public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes
public import Erdos1017.Exclusions.Cusp.CuspOutsideLargeCertificates

/-!
# Large-count outside split-gap contradiction

A positive split-value gap is incompatible with the large-count scalar reserve,
multiplier and coarse range bounds (`outside_large_contradiction`).
-/

@[expose] public section

namespace Erdos1017.CuspOutsideLargeSplitGap

/-- A positive actual split-value gap is incompatible with the displayed
large-count scalar reserve, multiplier and coarse range bounds. -/
theorem outside_large_contradiction {m ell x : ℝ} (hm : 9 ≤ m)
    (hell : 2 - 2 / m - 2 / (m + 1) ≤ ell) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hB : m * (m + 3) / (2 * (2 * m + 1)) ≤ x ^ 2)
    (hgap : 0 < m ^ 2 * Benchmark.splitValue (x / m) - (1 - 1 / m) -
      ell * (x ^ 2 - 1) / 2) : False := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m + 1 := by linarith
  have hr : x / m ∈ Set.Icc (0 : ℝ) (1 / 4) := by
    constructor
    · exact div_nonneg hx0 hm0.le
    · apply (div_le_iff₀ hm0).mpr
      linarith
  have hbound := Benchmark.splitValue_le_nineteen_twentieths hr
  have hscaled := mul_le_mul_of_nonneg_left hbound (pow_nonneg hm0.le 3)
  have hupper : m ^ 3 * ((x / m) ^ 2 * (1 - (19 / 20) * (x / m))) =
      m * x ^ 2 - (19 / 20) * x ^ 3 := by
    field_simp [hm0.ne']
  rw [hupper] at hscaled
  have hD : m * (1 - ell / 2) ≤ (2 * m + 1) / (m + 1) := by
    calc
      m * (1 - ell / 2) ≤ m * (1 - (2 - 2 / m - 2 / (m + 1)) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hm0.le
      _ = (2 * m + 1) / (m + 1) := by
        field_simp [hm0.ne', hm1.ne']
        ring
  have hpositive := mul_pos hm0 hgap
  have hgapIdentity : m * (m ^ 2 * Benchmark.splitValue (x / m) - (1 - 1 / m) -
      ell * (x ^ 2 - 1) / 2) = m ^ 3 * Benchmark.splitValue (x / m) - m + 1 -
        (m * ell / 2) * (x ^ 2 - 1) := by
    field_simp [hm0.ne']
    ring
  rw [hgapIdentity] at hpositive
  have henv : 0 < (m * (1 - ell / 2)) * (x ^ 2 - 1) + 1 - (19 / 20) * x ^ 3 := by
    nlinarith
  have hnegative := CuspOutsideLarge.outside_large_excess_neg hm hD hx0 hB
  nlinarith

end Erdos1017.CuspOutsideLargeSplitGap
