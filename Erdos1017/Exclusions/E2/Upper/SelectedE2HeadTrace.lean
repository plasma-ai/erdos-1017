module

public import Erdos1017.Exclusions.E2.Upper.E2TwoCenterScalar
public import Erdos1017.Exclusions.E2.Upper.SelectedE2ZeroBody
public import Erdos1017.SelectedModel.SelectedBodyEnergy
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyCubic

/-!
# No recovered common-peak head at the `E₂` contact

A recovered common-peak head is impossible at an `E₂` contact with
`q ∈ [1/10, 2/9]` (`no_e2_common_peak_head`); its positive physical body is
derived from the complete zero-body exclusion before the head budget is applied.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- An actual recovered common-peak head is impossible at the stated E2
contact. Its positive physical body is derived from the complete zero-body
exclusion; the head budget retains the same original multiplier and mass. -/
theorem no_e2_common_peak_head (R : S.ReverseRecovery) (r : S.I)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Icc (1 / 10 : ℝ) (2 / 9))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 2) (hr : r ∈ R.plateau)
    (hpeak : S.IsCommonForwardPeak d c r) : False := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], hq.2⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, _, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  let I := {x | S.ρ x = r.val}
  have hzero : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I ≠ 0 :=
    fun hz => S.no_e2_zero_body r hW hq' hdq hvalue hderiv hgap hglobal hz
  have hpositive := lt_of_le_of_ne (bodyPositiveEnergy_nonnegative W I) (Ne.symm hzero)
  rw [hW.bodyPositiveEnergy_eq_physicalBody hd hgap I (S.hfibers r.val r.property).1]
    at hpositive
  have htrace := R.common_peak_head_positive_body_trace r hr hW hd hgap hpeak hpositive
  have hbudget := R.common_peak_head_square_budget r hr hW hd hgap hpeak hcard
  apply LowerE2Scalar.not_two_center_head_trace hq (measureReal_nonneg : 0 ≤ μ.real I)
    hgamma.le
  · simpa only [hm, sub_eq_add_neg] using hbudget
  · have hmissing : 1 - 2 * d = LowerE2Scalar.missingMass q := by rw [hdq]; ring
    simpa only [hmissing] using htrace

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
