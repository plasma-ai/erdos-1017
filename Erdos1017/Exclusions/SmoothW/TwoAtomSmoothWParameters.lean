module

public import Erdos1017.Exclusions.SmoothW.FullSharpWPeak
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockMoments

/-!
# Own parameters of a four-region optimum at smooth `W`

Every own stationary four-region optimum at the smooth-`W` contact has an own
slope in the required range and a strict copy bonus, with a bound on the
independent `B` mass (`smoothW_own_parameters`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.TwoAtomCountGate

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m : ℝ}

/-- Every actual own stationary four-region optimum at the smooth-W
contact has the required own slope and strict copy bonus. The independent
B mass is bounded by the actual graph's missing density; no peak bound is assumed. -/
theorem smoothW_own_parameters (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → CappedModel.objective V - benchmark (density V) ≤
        CappedModel.objective W - benchmark (density W))
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hgraph : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) :
    -m ∈ Ioo (1 / 2 : ℝ) (2 / 3) ∧ 0 < 2 * (c - m * d) + m ∧
      μ.real (label ⁻¹' {1}) < 1 / 2 ∧
      μ.real (label ⁻¹' {1}) * (1 + m) < 2 * (2 * (c - m * d) + m) := by
  obtain ⟨_, _, hell, hdelta, hgamma, hmissing⟩ :=
    hW.smoothW_contact_parameters hd hgap he hactive hglobal
  have hdensity : density W = FiniteCappedSamplingCost.physicalDensity μ
      (fun a b => blockAdjacency (label a) (label b)) := by
    unfold density FiniteCappedSamplingCost.physicalDensity
    congr 1
    exact integral_congr_ae hgraph
  have hformula := block_physicalDensity (μ := μ) label hlabel
  rw [← hdensity, hW.density_eq] at hformula
  have ha : 0 ≤ μ.real (label ⁻¹' {0}) := measureReal_nonneg
  have hb : 0 ≤ μ.real (label ⁻¹' {1}) := measureReal_nonneg
  have hE : 0 ≤ μ.real (label ⁻¹' {3}) := measureReal_nonneg
  have hAE := mul_nonneg ha hE
  have hbhalf : μ.real (label ⁻¹' {1}) < 1 / 2 := by
    by_contra h
    have hlarge : 1 / 2 ≤ μ.real (label ⁻¹' {1}) := le_of_not_gt h
    nlinarith only [hformula, hmissing, hlarge, hAE,
      sq_nonneg (μ.real (label ⁻¹' {0}))]
  have hproduct := mul_nonneg (sub_nonneg.mpr hbhalf.le)
    (show 0 ≤ 1 + m by linarith [hell.2])
  refine ⟨hell, by linarith, hbhalf, ?_⟩
  nlinarith only [hproduct, hdelta, hgamma]

end Erdos1017.TwoAtomCountGate
