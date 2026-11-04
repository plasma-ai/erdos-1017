module

public import Erdos1017.Benchmark.BenchmarkCrossingBounds

/-!
# Scalar intercept bounds excluding a smooth point of `W`

Intercept bounds for the smooth mixed family: the stationary `W` intercept is
bounded strictly above `103/1000` by a rational whole-interval certificate, and
the small-peak selector cap and the active mixed branch are each shown
incompatible with it.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.SmoothWScalar

open Benchmark

/-- The smooth mixed-family intercept uses the same density, value and
own multiplier as the stationary benchmark profile. -/
theorem mixed_intercept_identity {s : ℝ} (hs : 0 < s) :
    2 * mixedValue s - (s + 1) / (3 * s) * (2 * mixedDensity s) =
      (-s ^ 3 + 7 * s ^ 2 - 2 * s - 1) / (3 * s * mixedDenominator s) := by
  have hD := (mixedDenominator_pos hs.le).ne'
  unfold mixedValue mixedDensity
  field_simp
  unfold mixedDenominator
  ring

/-- A rational whole-interval certificate bounds the stationary W
intercept strictly above 103/1000. -/
theorem mixed_intercept_gt {s : ℝ} (hs : s ∈ Icc (7 / 6 : ℝ) (19 / 15)) :
    103 / 1000 <
      2 * mixedValue s - (s + 1) / (3 * s) * (2 * mixedDensity s) := by
  have hs0 : 0 < s := by linarith [hs.1]
  rw [mixed_intercept_identity hs0]
  have hsq : s ^ 2 ≤ (19 / 15 : ℝ) ^ 2 := by
    gcongr
    exact hs.2
  have hsecant : 41167 / 25 ≤
      -1309 * (s ^ 2 + s * (7 / 6) + (7 / 6 : ℝ) ^ 2) +
        4528 * (s + 7 / 6) - 2618 := by
    nlinarith [hs.1, hs.2]
  have hproduct := mul_nonneg (sub_nonneg.mpr hs.1)
    (show 0 ≤ -1309 * (s ^ 2 + s * (7 / 6) + (7 / 6 : ℝ) ^ 2) +
      4528 * (s + 7 / 6) - 2618 by linarith)
  have hN : 0 < -1309 * s ^ 3 + 4528 * s ^ 2 - 2618 * s - 1000 := by
    nlinarith
  have hden : 0 < 3 * s * mixedDenominator s :=
    mul_pos (by positivity) (mixedDenominator_pos hs0.le)
  apply (lt_div_iff₀ hden).mpr
  unfold mixedDenominator
  nlinarith

private theorem multiplier_bounds {s : ℝ} (hs : s ∈ Icc (7 / 6 : ℝ) (19 / 15)) :
    (s + 1) / (3 * s) ∈ Ioo (0 : ℝ) (2 / 3) ∧
      1 - (s + 1) / (3 * s) < 101 / 250 := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hden : 0 < 3 * s := by positivity
  have hlo : (149 / 250 : ℝ) < (s + 1) / (3 * s) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [hs.2]
  constructor
  · constructor
    · exact div_pos (by linarith) hden
    · apply (div_lt_iff₀ hden).mpr
      linarith [hs.1]
  · linarith

/-- The two literal selector bounds share one endpoint hole mass.
Their affine envelope bounds the intercept without optimizing them separately. -/
theorem selector_intercept_bound {ell A C hF : ℝ}
    (hell : ell ∈ Icc (0 : ℝ) (2 / 3))
    (hC : C ≤ A ^ 2) (hH : 3 * C ≤ hF + A ^ 2) :
    2 * C - ell * hF ≤ 2 * (1 - ell) * A ^ 2 := by
  rcases le_total hF (2 * A ^ 2) with hlow | hhigh
  · have hp := mul_nonneg (sub_nonneg.mpr hell.2) (sub_nonneg.mpr hlow)
    nlinarith
  · have hp := mul_nonneg hell.1 (sub_nonneg.mpr hhigh)
    nlinarith

/-- The small-peak selector cap is incompatible with the original
smooth-W intercept and the literal density-paid forward comparison. -/
theorem small_selector_intercept_contradiction {s c C hF : ℝ}
    (hs : s ∈ Icc (7 / 6 : ℝ) (19 / 15)) (hc : mixedValue s < c)
    (hforward : 2 * c - (s + 1) / (3 * s) * (2 * mixedDensity s) ≤
      2 * C - (s + 1) / (3 * s) * hF)
    (hC : C ≤ 1 / 9) (hH : 3 * C ≤ hF + 1 / 9) : False := by
  have hb := multiplier_bounds hs
  have hselector := selector_intercept_bound
    (A := (1 / 3 : ℝ)) ⟨hb.1.1.le, hb.1.2.le⟩ (by norm_num; exact hC)
    (by norm_num; exact hH)
  have hfloor := mixed_intercept_gt hs
  nlinarith [hb.2]

/-- The actual active mixed branch cannot satisfy both the explicit
forward-selector intercept cap and the private-or-universal trace bound. -/
theorem active_mixed_trace_contradiction {e c A : ℝ}
    (he : e ∈ Icc epsilonStar epsilonD) (hactive : twoHeadCurve e ≤ mixedCurve e)
    (hc : mixedCurve e < c) (hA : 0 ≤ A)
    (hselector : 2 * c - (mixedInverse e + 1) / (3 * mixedInverse e) * (2 * e) ≤
      2 * (1 - (mixedInverse e + 1) / (3 * mixedInverse e)) * A ^ 2)
    (htrace : 3 * A ^ 2 +
      2 * A * (2 * c - (mixedInverse e + 1) / (3 * mixedInverse e) * (2 * e)) +
      (2 * c - (mixedInverse e + 1) / (3 * mixedInverse e) * (2 * e)) ^ 2 ≤ 4 * e) :
    False := by
  have hguards := active_mixed_parameter_guards he hactive
  have hi := mixedInverse_spec he
  have hs : mixedInverse e ∈ Icc (7 / 6 : ℝ) (19 / 15) :=
    ⟨hguards.1.le, hi.1.2.trans sigmaZero_lt_nineteen_fifteenths.le⟩
  have hcurve : mixedCurve e = mixedValue (mixedInverse e) := by
    rcases eq_or_lt_of_le he.1 with heq | hlt
    · rw [← heq]
      simp only [mixedCurve, le_refl, ite_true]
      exact mixed_branch_match.symm
    · simp only [mixedCurve, not_le.mpr hlt, ite_false, he.2, ite_true]
  rw [hcurve] at hc
  let ell := (mixedInverse e + 1) / (3 * mixedInverse e)
  let gamma := 2 * c - ell * (2 * e)
  change gamma ≤ 2 * (1 - ell) * A ^ 2 at hselector
  change 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 4 * e at htrace
  have hb := multiplier_bounds hs
  change ell ∈ Ioo (0 : ℝ) (2 / 3) ∧ 1 - ell < 101 / 250 at hb
  have hfloor := mixed_intercept_gt hs
  rw [hi.2] at hfloor
  have hgamma : 103 / 1000 < gamma := by
    dsimp [gamma, ell]
    linarith
  have hAsq : (103 / 808 : ℝ) < A ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hb.2.le) (sq_nonneg A)
    nlinarith
  have hAlo : (357 / 1000 : ℝ) < A := by
    by_contra h
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h))
      (show 0 ≤ A + 357 / 1000 by linarith)
    nlinarith
  have hA2 : (357 / 1000 : ℝ) ^ 2 < A ^ 2 := by
    gcongr
  have hcross : (357 / 1000 : ℝ) * (103 / 1000) < A * gamma := by
    gcongr
  have hgamma2 : (103 / 1000 : ℝ) ^ 2 < gamma ^ 2 := by
    gcongr
  nlinarith [hguards.2]

end Erdos1017.SmoothWScalar
