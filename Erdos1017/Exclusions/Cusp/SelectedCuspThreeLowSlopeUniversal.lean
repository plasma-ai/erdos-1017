module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopePeak
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeZeroBody
public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic

/-!
# No universal peak at the low-slope third cusp

At the third cusp with original multiplier below one, the common peak cannot be
universal; its positive-body premise is derived from the zero-body case
(`no_cusp_three_low_slope_universal_peak`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m d c : ℝ}

/-- At the third cusp with original multiplier below one, the actual
common peak cannot be universal. Its positive-body premise is derived
from the complete original zero-body exclusion. -/
theorem no_cusp_three_low_slope_universal_peak
    (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (huniv : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1) : False := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨_, hA, hmass⟩ := S.cusp_three_low_slope_peak_bounds i hdk hW hgap hglobal hell hpeak
  have hN := S.universal_atom_neutral i hW hd hgap huniv
  have hpositive : 0 < PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) {x | S.ρ x = i.val} := by
    have hne : PhysicalPrimal.bodyPositiveEnergy μ
        (Function.uncurry (chargeKernel W)) {x | S.ρ x = i.val} ≠ 0 :=
      fun hzero => S.no_cusp_three_zero_body i hW hdk hgap hglobal hzero
    exact lt_of_le_of_ne (bodyPositiveEnergy_nonnegative W _) (Ne.symm hne)
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap _ (S.hfibers i.val i.property).1]
    at hpositive
  have htrace := S.universal_positive_body_trace i hW hd hgap hN hpositive
  have hgamma := (hW.strict_gap_structure hd hgap).gamma_pos
  change 11 / 39 < μ.real {x | S.ρ x = i.val} at hA
  change 2 / 9 < 3 * (μ.real {x | S.ρ x = i.val}) ^ 2 at hmass
  have hcross := mul_nonneg
    (show 0 ≤ μ.real {x | S.ρ x = i.val} by linarith only [hA]) hgamma.le
  rw [hdk] at htrace hcross
  nlinarith only [hmass, htrace, hcross, sq_nonneg (2 * (c - m * (4 / 9)) + m)]

end Erdos1017.CappedModel.SelectedHighLowStructure
