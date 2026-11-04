module

public import Erdos1017.SelectedModel.Selection.QuadraticNullCorrection

/-!
# Tangent null directions under corrected competitors

A tangent direction with zero shifted quadratic energy has zero adjacency
quadratic energy whenever exact corrected competitors have nonpositive shifted
cost.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- A tangent direction with zero shifted quadratic energy has zero
adjacency quadratic energy whenever exact corrected competitors have
nonpositive shifted cost and the transverse square coefficient is positive. -/
theorem tangent_null_density_coefficient_eq_zero (a b c d α q : ℝ)
    (hb : 0 < b) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ t s : ℝ, |t| < ε → |s| < ε →
      a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2 = 0 →
      2 * α * t * s + q * s ^ 2 ≤ 0) : a = 0 := by
  let k := correctionFactor a b c d
  have hk : ContinuousAt k 0 := correctionFactor_continuousAt_zero a b c d hb
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * k t) 0 := by fun_prop
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ε :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hs' : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * k t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hmix : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 3 * (α * k t) ≤ 0 := by
    filter_upwards [ht, hs', correctionFactor_solves_eventually a b c d hb]
      with t ht hs hroot
    have h := hmax t (t ^ 2 * k t) ht hs hroot
    have hnonneg := mul_nonneg hq.le (sq_nonneg (t ^ 2 * k t))
    nlinarith
  have hlim : Tendsto (fun t => α * k t) (𝓝 (0 : ℝ)) (𝓝 (α * k 0)) :=
    hk.const_mul α
  have hright : α * k 0 ≤ 0 := by
    apply le_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
    filter_upwards [hmix.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hmix ht
    exact nonpos_of_mul_nonpos_right hmix (pow_pos (show 0 < t from ht) 3)
  have hleft : 0 ≤ α * k 0 := by
    apply ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ))))
    filter_upwards [hmix.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hmix ht
    have hneg : (-t) ^ 3 * (-(α * k t)) ≤ 0 := by
      convert hmix using 1
      ring
    have h := nonpos_of_mul_nonpos_right hneg (pow_pos (neg_pos.mpr ht) 3)
    linarith
  have hprod : α * k 0 = 0 := le_antisymm hright hleft
  by_cases ha : a = 0
  · exact ha
  have hk0 : k 0 ≠ 0 := by
    dsimp only [k]
    rw [correctionFactor_zero a b c d hb]
    exact div_ne_zero (neg_ne_zero.mpr ha) hb.ne'
  have hα : α = 0 := (mul_eq_zero.mp hprod).resolve_right hk0
  exact (null_density_coefficients_eq_zero 0 a b c d q hb hq ε hε (by
    intro t s ht hs hroot
    have h := hmax t s ht hs (by simpa only [zero_mul, zero_add] using hroot)
    simpa only [hα, mul_zero, zero_mul, zero_add] using h)).2

end Erdos1017.Variation
