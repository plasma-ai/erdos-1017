module

public import Erdos1017.LowerBound.WeightedGraphTwoHeadLower
public import Erdos1017.Benchmark.BenchmarkProperties

/-!
# Finite-graph lower bounds for every benchmark branch

The mixed, linear mixed and two-head parameter curves lie below the density
limit, so every branch of the benchmark is realized from below by finite graphs
(`benchmark_le_densityLimit`). It is used in the integer benchmark lower bound
and the global excess maximum.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators
open FractionalGraph Benchmark

theorem mixed_parameter_lower (s : ℝ) (hs : s ∈ Set.Icc sigmaD sigmaZero) :
    mixedValue s ≤ densityLimit (1 / 2 - mixedDensity s) := by
  have hs₁ : 1 ≤ s := sigmaD_spec.1.1.trans hs.1
  have hQ := mixedDenominator_pos (show 0 ≤ s by linarith)
  let a := (-3 * s ^ 2 + 3 * s + 1) / mixedDenominator s
  let b := (4 * s + 1) / mixedDenominator s
  let u := s * (4 * s + 1) / mixedDenominator s
  have hroot : 3 * sigmaZero ^ 2 - 3 * sigmaZero - 1 = 0 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
    unfold sigmaZero
    nlinarith
  have ha : 0 ≤ a := by
    apply div_nonneg _ hQ.le
    have hsigma : 1 ≤ sigmaZero := hs₁.trans hs.2
    have hprod := mul_nonneg (sub_nonneg.mpr hs.2)
      (show 0 ≤ 3 * (sigmaZero + s) - 3 by linarith)
    nlinarith [hprod]
  have hb : 0 ≤ b := div_nonneg (by linarith) hQ.le
  have hu : 0 ≤ u := div_nonneg (mul_nonneg (by linarith) (by linarith)) hQ.le
  have hsum : a + b + u = 1 := by
    dsimp [a, b, u]
    field_simp
    simp [mixedDenominator]
    ring
  have h := leaf_limit_lower 2 (by decide) a b u ha hb hu hsum
  have hvalue : a * b + 2 / ((2 : ℕ) + 1 : ℝ) * b * u -
      u ^ 2 / ((2 : ℝ) * (2 + 1)) = mixedValue s := by
    dsimp [a, b, u]
    unfold mixedValue
    field_simp
    ring
  have hdensity : a * b + b * u + u ^ 2 / 2 = 1 / 2 - mixedDensity s := by
    dsimp [a, b, u]
    unfold mixedDensity
    field_simp
    simp only [mixedDenominator]
    ring
  norm_num only [Nat.cast_ofNat] at h hvalue
  rw [hvalue, hdensity] at h
  exact h

theorem twoHead_parameter_lower (z : ℝ) (hz : z ∈ Set.Icc (2 / 3 : ℝ) zC) :
    twoHeadValue z ≤ densityLimit (1 / 2 - twoHeadDensity z) := by
  have hz₀ : 0 ≤ z := by linarith [hz.1]
  have hz₁ : z ≤ 1 := by linarith [hz.2, zC_spec.1.2]
  have hη := twoHeadDenominator_pos hz.1
  let a := z * (5 * z - 3) / (4 * twoHeadDenominator z)
  let b := z * (1 - z) / (4 * twoHeadDenominator z)
  let u := (3 * z - 2) / (2 * twoHeadDenominator z)
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hz₀ (by linarith [hz.1])) (by positivity)
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hz₀ (sub_nonneg.mpr hz₁)) (by positivity)
  have hu : 0 ≤ u := div_nonneg (by linarith [hz.1]) (by positivity)
  have hsum : a + b + u = 1 := by
    dsimp [a, b, u]
    field_simp
    simp only [twoHeadDenominator]
    ring
  have h := complete_twoHead_limit_lower a b u ha hb hu hsum
  have hvalue : a * b + (2 / 3) * (a - b) * u - u ^ 2 / 6 = twoHeadValue z := by
    dsimp [a, b, u]
    unfold twoHeadValue twoHeadDensity
    field_simp
    ring
  have hdensity : (1 - a ^ 2 - b ^ 2) / 2 = 1 / 2 - twoHeadDensity z := by
    dsimp [a, b, u]
    unfold twoHeadDensity
    field_simp
    simp only [twoHeadDenominator]
    ring
  rw [hvalue, hdensity] at h
  exact h

theorem epsilonD_gt_eighth : (1 / 8 : ℝ) < epsilonD := by
  have hσ : sigmaD ≤ sigmaZero := by linarith [sigmaD_spec.1.2, sigmaZero_bounds.1]
  have h := mixedDensity_strictAntiOn.antitoneOn ⟨le_rfl, hσ⟩
    ⟨sigmaD_spec.1.2, sigmaZero_bounds.1.le⟩ sigmaD_spec.1.2
  have hv : (1 / 8 : ℝ) < mixedDensity (11 / 10) := by
    norm_num [mixedDensity, mixedDenominator]
  exact hv.trans_le h

theorem linear_mixed_lower (ε : ℝ) (hε : ε ∈ Set.Icc (1 / 8 : ℝ) (1 / 4)) :
    ε ≤ densityLimit (1 / 2 - ε) := by
  let u := Real.sqrt (1 / 2 - 2 * ε)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu₂ : u ^ 2 = 1 / 2 - 2 * ε := Real.sq_sqrt (by linarith [hε.2])
  have hu₁ : u ≤ 1 / 2 := by nlinarith [hε.1]
  have h := leaf_limit_lower 1 (by decide) (1 / 2 - u) (1 / 2) u
    (by linarith) (by norm_num) hu (by ring)
  have hleft : (1 / 2 - u) * (1 / 2) + 2 / ((1 : ℕ) + 1 : ℝ) * (1 / 2) * u -
      u ^ 2 / ((1 : ℝ) * (1 + 1)) = ε := by nlinarith
  have hright : (1 / 2 - u) * (1 / 2) + (1 / 2) * u + u ^ 2 / 2 = 1 / 2 - ε := by nlinarith
  norm_num only [Nat.cast_ofNat] at h hleft
  rwa [hleft, hright] at h

theorem mixedCurve_le_densityLimit (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    mixedCurve ε ≤ densityLimit (1 / 2 - ε) := by
  unfold mixedCurve
  split_ifs with hstar hD
  · exact split_curve_le_densityLimit ε ⟨hε.1, by linarith [hε.2]⟩
  · have hspec := mixedInverse_spec (show ε ∈ Set.Icc epsilonStar epsilonD by
      exact ⟨le_of_not_ge hstar, hD⟩)
    have h := mixed_parameter_lower (mixedInverse ε) hspec.1
    rwa [hspec.2] at h
  · exact linear_mixed_lower ε ⟨by linarith [epsilonD_gt_eighth], hε.2⟩

theorem twoHeadCurve_le_densityLimit (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    twoHeadCurve ε ≤ densityLimit (1 / 2 - ε) := by
  unfold twoHeadCurve
  split_ifs with hzero hC
  · exact densityLimit_nonneg _
  · exact split_curve_le_densityLimit ε ⟨hε.1, by linarith [hε.2]⟩
  · have hspec := twoHeadInverse_spec (show ε ∈ Set.Icc epsilonC (1 / 4) by
      exact ⟨le_of_not_ge hC, hε.2⟩)
    have h := twoHead_parameter_lower (twoHeadInverse ε) hspec.1
    rwa [hspec.2] at h

/-- Every branch of the proposed benchmark is realized from below by actual finite graphs. -/
theorem benchmark_le_densityLimit (d : ℝ) (hd : d ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Erdos1017.benchmark d ≤ densityLimit d := by
  by_cases hquarter : d ≤ 1 / 4
  · rw [Erdos1017.benchmark_of_le_quarter hquarter, densityLimit_eq_self d ⟨hd.1, hquarter⟩]
  · by_cases hhalf : d < 1 / 2
    · have hε : 1 / 2 - d ∈ Set.Icc (0 : ℝ) (1 / 4) := by constructor <;> linarith
      have hm := mixedCurve_le_densityLimit (1 / 2 - d) hε
      have ht := twoHeadCurve_le_densityLimit (1 / 2 - d) hε
      have heq : 1 / 2 - (1 / 2 - d) = d := by ring
      rw [heq] at hm ht
      simp only [Erdos1017.benchmark, ite_eq_right hquarter, ite_eq_left hhalf]
      exact max_le hm ht
    · simp only [Erdos1017.benchmark, ite_eq_right hquarter, ite_eq_right hhalf]
      exact densityLimit_nonneg d

end Erdos1017.WeightedGraph
