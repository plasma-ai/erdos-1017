module

public import Erdos1017.Models.Selection.QuadraticConstraint

/-!
# One-sided tangent condition at a right local maximum

A feasible surgery available only for positive parameters forces its linear gain
to be nonpositive after exact quadratic density correction
(`tangent_linear_nonpos_of_right_local_max`).
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- A feasible surgery available only for positive parameters still forces
its linear gain to be nonpositive after exact quadratic density correction. -/
theorem tangent_linear_nonpos_of_right_local_max
    (a b c d L M A C D : ℝ) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ t s : ℝ, 0 < t → t < ε → |s| < ε →
      a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2 = 0 →
      L * t + M * s + A * t ^ 2 + 2 * C * t * s + D * s ^ 2 ≤ 0) : L ≤ 0 := by
  let q := correctionFactor a b c d
  have hq : ContinuousAt q 0 := correctionFactor_continuousAt_zero a b c d hb
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * q t) 0 := by fun_prop
  have hsmallt : ∀ᶠ t in 𝓝 (0 : ℝ), t < ε := gt_mem_nhds hε
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * q t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hcost : ContinuousAt
      (fun t : ℝ => L + M * t * q t + A * t + 2 * C * t ^ 2 * q t + D * t ^ 3 * (q t) ^ 2) 0 := by
    fun_prop
  have hlim : Tendsto
      (fun t : ℝ => L + M * t * q t + A * t + 2 * C * t ^ 2 * q t + D * t ^ 3 * (q t) ^ 2)
      (𝓝[>] 0) (𝓝 L) := by
    simpa using hcost.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  apply le_of_tendsto hlim
  filter_upwards [hpos, hsmallt.filter_mono nhdsWithin_le_nhds,
    hsmalls.filter_mono nhdsWithin_le_nhds,
    (correctionFactor_solves_eventually a b c d hb).filter_mono nhdsWithin_le_nhds]
    with t ht hsmallt hsmalls hroot
  have h := hmax t (t ^ 2 * q t) ht hsmallt hsmalls hroot
  have hm : t * (L + M * t * q t + A * t + 2 * C * t ^ 2 * q t + D * t ^ 3 * (q t) ^ 2) ≤ 0 := by
    convert h using 1
    ring
  exact nonpos_of_mul_nonpos_right hm ht

end Erdos1017.Variation
