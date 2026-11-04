module

public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWOneCenterGeometry
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWPrivateExclusion
public import Erdos1017.Exclusions.SmoothW.SelectedSmoothWZeroBody
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalNeutral

/-!
# No one-center recovery with positive source at smooth `W`

A one-center reverse recovery with positive entire original compulsory source is
impossible at smooth-`W` contact; the private and saturated-universal branches
are both excluded (`no_smoothW_one_center_nonempty_source`).
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

/-- An actual one-center reverse recovery with positive entire original
compulsory source is impossible at smooth-W contact. The private and
saturated-universal branches are derived for the same original peak. -/
theorem no_smoothW_one_center_nonempty_source (R : S.ReverseRecovery)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (he : 1 / 2 - d ∈ Ioo Benchmark.epsilonStar Benchmark.epsilonD)
    (hactive : Benchmark.twoHeadCurve (1 / 2 - d) < Benchmark.mixedCurve (1 / 2 - d))
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hcard : R.plateau.card = 1)
    (hsource : 0 < μ (S.reverseCompulsorySource R.plateau)) : False := by
  obtain ⟨_, k, _, _, _, hpeak, _, _⟩ :=
    S.exists_sharp_smoothW_peak hW hd hgap he hactive hglobal
  change S.IsCommonForwardPeak d c k at hpeak
  obtain ⟨p, _, hkp, hcase⟩ :=
    R.exists_smoothW_one_center_peak_geometry hW hd hgap he hactive hglobal
      hcard hsource k hpeak
  rcases hcase with hprivate | ⟨hpair, huniv⟩
  · exact S.no_smoothW_private_common_peak k p hkp hW hd hgap he hactive hglobal
      hpeak hprivate
  have hN := S.universal_atom_neutral k hW hd hgap huniv
  let I := {x | S.ρ x = k.val}
  have hI : MeasurableSet I := (S.hfibers k.val k.property).1
  have hnonnegative : 0 ≤ PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I :=
    integral_nonneg (fun z => sq_nonneg (max (chargeKernel W z.1 z.2) 0))
  by_cases hzero : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I = 0
  · exact S.no_smoothW_saturated_zero_body k p hW hd hgap he hactive hglobal
      hpair hzero
  have hcharge := PhysicalRepresentative.charge_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support
  have henergy : PhysicalPrimal.bodyPositiveEnergy μ
      (Function.uncurry (chargeKernel W)) I =
      ∫ z : Ω × Ω,
        (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m) I z.1 z.2) ^ 2
          ∂μ.prod μ := by
    rw [PhysicalPrimal.bodyPositiveEnergy, ← integral_indicator (hI.compl.prod hI.compl)]
    apply integral_congr_ae
    filter_upwards [hcharge] with z hz
    by_cases h : z.1 ∉ I ∧ z.2 ∉ I
    · simp [IndependentAtomCopy.positiveBody, Function.uncurry, h, hz]
    · simp [IndependentAtomCopy.positiveBody, h]
  have hpositive := lt_of_le_of_ne hnonnegative (Ne.symm hzero)
  rw [henergy] at hpositive
  exact S.no_smoothW_universal_peak_positive_body k hW hd hgap he hactive hglobal
    hpeak hN hpositive

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
