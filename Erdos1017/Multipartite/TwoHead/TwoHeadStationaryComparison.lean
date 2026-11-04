module

public import Erdos1017.Multipartite.BenchmarkLowDensityGuards
public import Erdos1017.Benchmark.SplitCurve

/-!
# Scalar comparisons of the stationary two-head formulas

Exact comparisons between the stationary two-head formulas, their piecewise
curve and the split comparator. These are scalar curve facts; they do not assume
the optimization of a two-head profile.
-/

@[expose] public section

namespace Erdos1017.Benchmark

theorem twoHeadDensity_bounds_full {z : ℝ} (hz : z ∈ Set.Icc (2 / 3 : ℝ) (4 / 5)) :
    twoHeadDensity z ∈ Set.Icc (13 / 121 : ℝ) (1 / 4) := by
  have hlo := twoHeadDensity_strictAntiOn_full.antitoneOn hz
    (show (4 / 5 : ℝ) ∈ Set.Icc (2 / 3) (4 / 5) by norm_num) hz.2
  have hhi := twoHeadDensity_strictAntiOn_full.antitoneOn
    (show (2 / 3 : ℝ) ∈ Set.Icc (2 / 3) (4 / 5) by norm_num) hz hz.1
  rw [show twoHeadDensity (4 / 5) = 13 / 121 by norm_num [twoHeadDensity, twoHeadDenominator]] at hlo
  rw [twoHeadDensity_two_thirds] at hhi
  exact ⟨hlo, hhi⟩

theorem twoHead_split_square_gap {z : ℝ} (hz : 2 / 3 ≤ z) :
    (twoHeadValue z + 5 / 3 * twoHeadDensity z + 1 / 6) ^ 2 - 2 * twoHeadDensity z =
      z ^ 2 * (z - 1) ^ 2 * twoHeadRootPolynomial z / (576 * twoHeadDenominator z ^ 4) := by
  have hd := (twoHeadDenominator_pos hz).ne'
  unfold twoHeadValue twoHeadDensity twoHeadRootPolynomial
  field_simp
  unfold twoHeadDenominator
  ring

theorem twoHeadRootPolynomial_pos_below_three_quarters {z : ℝ}
    (hz : z ∈ Set.Icc (2 / 3 : ℝ) (3 / 4)) : 0 < twoHeadRootPolynomial z := by
  have hid : twoHeadRootPolynomial z = 25 / 256 + (3 / 4 - z) *
      (95 * (z - 2 / 3) ^ 3 + (973 / 4) * (z - 2 / 3) ^ 2 +
        (2141 / 48) * (z - 2 / 3) + 5143 / 1728) := by
    unfold twoHeadRootPolynomial
    ring
  rw [hid]
  have ht : 0 ≤ z - 2 / 3 := sub_nonneg.mpr hz.1
  have hu : 0 ≤ 3 / 4 - z := sub_nonneg.mpr hz.2
  positivity

theorem twoHeadRootPolynomial_nonneg_of_le_zC {z : ℝ} (hz : 2 / 3 ≤ z) (hzc : z ≤ zC) :
    0 ≤ twoHeadRootPolynomial z := by
  by_cases hlo : z ≤ 3 / 4
  · exact (twoHeadRootPolynomial_pos_below_three_quarters ⟨hz, hlo⟩).le
  have h := twoHeadRootPolynomial_strictAntiOn.antitoneOn
    (show z ∈ Set.Ici (3 / 4 : ℝ) from (lt_of_not_ge hlo).le)
    zC_spec.1.1 hzc
  rwa [zC_spec.2] at h

theorem twoHeadValue_le_twoHeadCurve_density {z : ℝ}
    (hz : z ∈ Set.Icc (2 / 3 : ℝ) (4 / 5)) :
    twoHeadValue z ≤ twoHeadCurve (twoHeadDensity z) := by
  have he := twoHeadDensity_bounds_full hz
  have he0 : twoHeadDensity z ≠ 0 := by linarith [he.1]
  by_cases hzc : z ≤ zC
  · have heC : epsilonC ≤ twoHeadDensity z :=
      twoHeadDensity_strictAntiOn.antitoneOn ⟨hz.1, hzc⟩
        ⟨by linarith [zC_spec.1.1], le_rfl⟩ hzc
    have hinv := twoHeadInverse_unique ⟨heC, he.2⟩ ⟨hz.1, hzc⟩ rfl
    simp only [twoHeadCurve, he0, ite_false]
    split_ifs with hle
    · have heq : twoHeadDensity z = epsilonC := le_antisymm hle heC
      have hzEq : z = zC := twoHeadDensity_strictAntiOn.injOn
        ⟨hz.1, hzc⟩ ⟨by linarith [zC_spec.1.1], le_rfl⟩ heq
      rw [hzEq]
      exact twoHeadValue_zC.le
    · rw [← hinv]
  · have hzgt : zC < z := lt_of_not_ge hzc
    have heC : twoHeadDensity z < epsilonC :=
      twoHeadDensity_strictAntiOn_full
        ⟨by linarith [zC_spec.1.1], zC_spec.1.2⟩ hz hzgt
    have hp := twoHeadRootPolynomial_strictAntiOn.antitoneOn
      zC_spec.1.1 (zC_spec.1.1.trans hzgt.le) hzgt.le
    rw [zC_spec.2] at hp
    have hgap := twoHead_split_square_gap hz.1
    have hnonpos : z ^ 2 * (z - 1) ^ 2 * twoHeadRootPolynomial z /
        (576 * twoHeadDenominator z ^ 4) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hp)
        (by positivity)
    have hr0 := Real.sqrt_nonneg (2 * twoHeadDensity z)
    have hrsq := Real.sq_sqrt (show 0 ≤ 2 * twoHeadDensity z by linarith [he.1])
    have hr : Real.sqrt (2 * twoHeadDensity z) ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
      constructor <;> nlinarith [he.1, epsilonC_lt_nine_eightieths]
    have hvalue := twoHeadValue_ge_density hz
    have harg : 0 ≤ twoHeadValue z + 5 / 3 * twoHeadDensity z + 1 / 6 := by linarith [he.1]
    have hle : twoHeadValue z + 5 / 3 * twoHeadDensity z + 1 / 6 ≤
        Real.sqrt (2 * twoHeadDensity z) := by nlinarith
    simp only [twoHeadCurve, he0, ite_false, heC.le, ite_true]
    rw [splitValue_on_cell 1 (by
      norm_num only [Nat.cast_one]
      exact hr)]
    norm_num only [splitPolynomial, Nat.cast_ofNat]
    nlinarith

theorem splitValue_le_twoHeadCurve {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    splitValue (Real.sqrt (2 * e)) ≤ twoHeadCurve e := by
  by_cases he0 : e = 0
  · simp [he0, twoHeadCurve, splitValue]
  by_cases heC : e ≤ epsilonC
  · simp [twoHeadCurve, he0, heC]
  have hegt : epsilonC < e := lt_of_not_ge heC
  by_cases heighth : 1 / 8 ≤ e
  · have hr0 := Real.sqrt_nonneg (2 * e)
    have hrsq := Real.sq_sqrt (show 0 ≤ 2 * e by linarith [he.1])
    have hr : Real.sqrt (2 * e) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
      constructor <;> nlinarith [he.2]
    have hsplit : splitValue (Real.sqrt (2 * e)) ≤ e := by
      rw [splitValue_on_cell 0 (by
        norm_num only [Nat.cast_zero, zero_add, one_div_one]
        exact hr)]
      norm_num only [splitPolynomial, Nat.cast_ofNat]
      nlinarith [sq_nonneg (Real.sqrt (2 * e) - 1 / 2)]
    exact hsplit.trans (twoHeadCurve_ge_epsilon_of_eighth_le ⟨heighth, he.2⟩)
  · have hi := twoHeadInverse_spec ⟨hegt.le, he.2⟩
    have hz : twoHeadInverse e ∈ Set.Icc (2 / 3 : ℝ) (4 / 5) :=
      ⟨hi.1.1, hi.1.2.trans zC_spec.1.2⟩
    have hp := twoHeadRootPolynomial_nonneg_of_le_zC hi.1.1 hi.1.2
    have hgap := twoHead_split_square_gap hi.1.1
    rw [hi.2] at hgap
    have hnonneg : 0 ≤ (twoHeadInverse e) ^ 2 * (twoHeadInverse e - 1) ^ 2 *
        twoHeadRootPolynomial (twoHeadInverse e) /
          (576 * twoHeadDenominator (twoHeadInverse e) ^ 4) := by positivity
    have hr0 := Real.sqrt_nonneg (2 * e)
    have hrsq := Real.sq_sqrt (show 0 ≤ 2 * e by linarith [he.1])
    have hr : Real.sqrt (2 * e) ∈ Set.Icc (1 / 3 : ℝ) (1 / 2) := by
      constructor <;> nlinarith [tenth_lt_epsilonC]
    have hvalue := twoHeadValue_ge_density hz
    rw [hi.2] at hvalue
    have harg : 0 ≤ twoHeadValue (twoHeadInverse e) + 5 / 3 * e + 1 / 6 := by
      linarith [he.1]
    have hle : Real.sqrt (2 * e) ≤ twoHeadValue (twoHeadInverse e) + 5 / 3 * e + 1 / 6 := by
      nlinarith
    simp only [twoHeadCurve, he0, ite_false, heC]
    rw [splitValue_on_cell 1 (by
      norm_num only [Nat.cast_one]
      exact hr)]
    norm_num only [splitPolynomial, Nat.cast_ofNat]
    nlinarith

end Erdos1017.Benchmark
