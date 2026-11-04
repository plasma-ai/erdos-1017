module

public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Positive second derivative at a smooth contact

A smooth benchmark contact of a strict-gap `FullStationaryClass` model has
positive second derivative; the positive bounded direction and the multiplier
identification are derived.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A smooth benchmark contact of the actual strict-gap model has positive
second derivative. The positive bounded direction and original multiplier
identification are derived from that same displayed model. -/
theorem FullStationaryClass.benchmark_second_deriv_pos_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hB : ContDiffAt ℝ 2 benchmark d) : 0 < deriv (deriv benchmark) d := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  obtain ⟨u, hpositive⟩ := exists_positive_direction_of_eigenvector W m
    w hw hmean σ hσ heigen
  have hBW : ContDiffAt ℝ 2 benchmark (density W) := hW.density_eq ▸ hB
  have hm := full_stationary_multiplier_eq_benchmark_deriv W hW.full hglobal
    (hBW.differentiableAt (by norm_num)).hasDerivAt m _ hW.stationary hs.nonconstant_degree
  have hcurvature := full_benchmark_curvature W hW.full hglobal hBW u
  rw [← hm, ← shiftedOperator_eq] at hcurvature
  change 0 < ⟪shiftedOperator W m (Variation.directionToL2 u),
    Variation.directionToL2 u⟫ at hpositive
  have hsecond : 0 < deriv (deriv benchmark) (density W) := by
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot)
      (sq_nonneg ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 u⟫)
    exact (not_le_of_gt hpositive) (hcurvature.trans hnonpos)
  rwa [hW.density_eq] at hsecond

end Erdos1017.CappedModel
