module

public import Erdos1017.ContactLocation.QuadraticOneSidedContact
public import Erdos1017.ContactLocation.FullCuspContact

/-!
# Multiplier differs from concave one-sided slopes

For a strict-gap `FullStationaryClass` model, the multiplier cannot equal the
slope of a concave smooth right-side benchmark extension, nor the corresponding
concave left-side slope.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem quadratic_density_right {d a q : ℝ} (ha : 0 < a) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ici 0), d + t * a + t ^ 2 * q / 2 ∈ Ici d := by
  have hc : ContinuousAt (fun t : ℝ => a + t * q / 2) 0 := by fun_prop
  have hpositive : ∀ᶠ t in nhds (0 : ℝ), 0 < a + t * q / 2 :=
    hc.eventually (eventually_gt_nhds (by simpa using ha))
  filter_upwards [hpositive.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with t ht ht0
  change d ≤ d + t * a + t ^ 2 * q / 2
  have ht0 : 0 ≤ t := ht0
  nlinarith [mul_nonneg ht0 ht.le]

private theorem quadratic_density_left {d a q : ℝ} (ha : a < 0) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ici 0), d + t * a + t ^ 2 * q / 2 ∈ Iic d := by
  have hc : ContinuousAt (fun t : ℝ => a + t * q / 2) 0 := by fun_prop
  have hnegative : ∀ᶠ t in nhds (0 : ℝ), a + t * q / 2 < 0 :=
    hc.eventually (eventually_lt_nhds (by simpa using ha))
  filter_upwards [hnegative.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with t ht ht0
  change d + t * a + t ^ 2 * q / 2 ≤ d
  have ht0 : 0 ≤ t := ht0
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0 ht.le]

private theorem full_side_curvature (W : Model Ω μ) (hW : FullFeasible W)
    (hglobal : ∀ (η : Measure Ω) [IsProbabilityMeasure η] (U : Model Ω η),
      FullFeasible U → objective U - benchmark (density U) ≤
        objective W - benchmark (density W))
    (β : ℝ → ℝ) (hβ : ContDiffAt ℝ 2 β (density W)) (s : Set ℝ)
    (hside : β =ᶠ[nhdsWithin (density W) s] benchmark)
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hm : m = deriv β (density W)) (f : Variation.WeightDirections μ)
    (hmaps : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ici 0),
      density W + t * (Variation.weightFirstVariation (adjacencyOperator W) f / 2) +
        t ^ 2 * Variation.weightSecondVariation (adjacencyOperator W) f f / 2 ∈ s) :
    Variation.weightSecondVariation (shiftedOperator W m) f f ≤
      deriv (deriv β) (density W) *
        (Variation.weightFirstVariation (adjacencyOperator W) f / 2) ^ 2 := by
  let D := fun t : ℝ => density W +
    t * (Variation.weightFirstVariation (adjacencyOperator W) f / 2) +
    t ^ 2 * Variation.weightSecondVariation (adjacencyOperator W) f f / 2
  let Y := fun t : ℝ => objective W +
    t * (Variation.weightFirstVariation (chargeOperator W) f / 2) +
    t ^ 2 * Variation.weightSecondVariation (chargeOperator W) f f / 2
  have hD0 : D 0 = density W := by simp [D]
  have hc : ContinuousAt D 0 := by fun_prop
  have hDt : Tendsto D (nhdsWithin (0 : ℝ) (Ici 0)) (nhds (density W)) := by
    simpa only [hD0] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hwithin : Tendsto D (nhdsWithin (0 : ℝ) (Ici 0)) (nhdsWithin (density W) s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hDt, hmaps⟩
  have heq : (fun t => Y t - benchmark (D t)) =ᶠ[nhdsWithin (0 : ℝ) (Ici 0)]
      (fun t => Y t - β (D t)) := by
    filter_upwards [hside.comp_tendsto hwithin] with t ht
    change β (D t) = benchmark (D t) at ht
    rw [ht]
  have hraw : IsLocalMaxOn (fun t => Y t - benchmark (D t)) (Ici 0) 0 :=
    (full_benchmark_reweight_local_max W hW hglobal f).filter_mono nhdsWithin_le_nhds
  have hmax := hraw.congr heq (show (0 : ℝ) ∈ Ici 0 from le_rfl)
  have hstationary := LinearMap.congr_fun
    (firstVariation_identity_of_shifted_zero W m
      (shiftedFirstVariation_zero_of_stationary W m ν hrow)) f
  simp only [LinearMap.smul_apply, smul_eq_mul] at hstationary
  have hfirst : Variation.weightFirstVariation (chargeOperator W) f / 2 =
      deriv β (density W) * (Variation.weightFirstVariation (adjacencyOperator W) f / 2) := by
    rw [hstationary, hm]
    ring
  have hcurvature := SmoothContact.quadratic_right_curvature hβ hfirst hmax
  change Variation.weightSecondVariation (chargeOperator W) f f -
    deriv β (density W) * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ _ at hcurvature
  rw [← hm] at hcurvature
  change ⟪shiftedOperator W m (Variation.directionToL2 f), Variation.directionToL2 f⟫ ≤ _
  change ⟪chargeOperator W (Variation.directionToL2 f), Variation.directionToL2 f⟫ -
    m * ⟪adjacencyOperator W (Variation.directionToL2 f), Variation.directionToL2 f⟫ ≤ _ at hcurvature
  simpa only [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left,
    real_inner_smul_left] using hcurvature

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

private theorem FullStationaryClass.exists_positive_energy_positive_degree
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ f : Variation.WeightDirections μ,
      0 < Variation.weightFirstVariation (adjacencyOperator W) f ∧
        0 < Variation.weightSecondVariation (shiftedOperator W m) f f := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hmean σ hσ heigen
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hfirst := shiftedFirstVariation_zero_of_stationary W m _ hW.stationary
  have htrans := full_positive_direction_transverse W hW.full hopt m hfirst hs.regular u hq
  rcases lt_or_gt_of_ne htrans with hneg | hpos
  · refine ⟨-u, ?_, ?_⟩
    · simpa only [map_neg] using neg_pos.mpr hneg
    · change 0 < ⟪shiftedOperator W m (Variation.directionToL2 (-u)),
        Variation.directionToL2 (-u)⟫
      change 0 < ⟪shiftedOperator W m (Variation.directionToL2 u),
        Variation.directionToL2 u⟫ at hq
      simpa only [map_neg, inner_neg_left, inner_neg_right, neg_neg] using hq
  · exact ⟨u, hpos, hq⟩

/-- The original multiplier cannot equal the slope of a concave smooth
right-side benchmark extension. The positive transverse tilt and its
actual density-side inclusion are constructed from the same model. -/
theorem FullStationaryClass.multiplier_ne_right_concave_slope_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hglobal : ∀ (η : Measure Ω) [IsProbabilityMeasure η] (U : Model Ω η),
      FullFeasible U → objective U - benchmark (density U) ≤
        objective W - benchmark (density W))
    (β : ℝ → ℝ) (hβ : ContDiffAt ℝ 2 β d) (hconcave : deriv (deriv β) d ≤ 0)
    (hside : β =ᶠ[nhdsWithin d (Ici d)] benchmark) : m ≠ deriv β d := by
  intro hm
  obtain ⟨f, ha, hq⟩ := hW.exists_positive_energy_positive_degree hd hgap
  have hβW : ContDiffAt ℝ 2 β (density W) := hW.density_eq ▸ hβ
  have hmW : m = deriv β (density W) := by simpa only [hW.density_eq] using hm
  have hsideW : β =ᶠ[nhdsWithin (density W) (Ici (density W))] benchmark :=
    hW.density_eq ▸ hside
  have hcurvature := full_side_curvature W hW.full hglobal β hβW (Ici (density W))
    hsideW m _ hW.stationary hmW f (quadratic_density_right (by positivity))
  have hnonpos : deriv (deriv β) (density W) *
      (Variation.weightFirstVariation (adjacencyOperator W) f / 2) ^ 2 ≤ 0 := by
    rw [hW.density_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hconcave (sq_nonneg _)
  exact (not_le_of_gt hq) (hcurvature.trans hnonpos)

/-- The corresponding concave left-side slope is also impossible. The
opposite actual tilt is still positive in shifted energy and sends its
small positive parameter into the left density side. -/
theorem FullStationaryClass.multiplier_ne_left_concave_slope_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hglobal : ∀ (η : Measure Ω) [IsProbabilityMeasure η] (U : Model Ω η),
      FullFeasible U → objective U - benchmark (density U) ≤
        objective W - benchmark (density W))
    (β : ℝ → ℝ) (hβ : ContDiffAt ℝ 2 β d) (hconcave : deriv (deriv β) d ≤ 0)
    (hside : β =ᶠ[nhdsWithin d (Iic d)] benchmark) : m ≠ deriv β d := by
  intro hm
  obtain ⟨f, ha, hq⟩ := hW.exists_positive_energy_positive_degree hd hgap
  have hnegative : Variation.weightFirstVariation (adjacencyOperator W) (-f) < 0 := by
    simpa only [map_neg] using neg_neg_of_pos ha
  have hpositive : 0 < Variation.weightSecondVariation (shiftedOperator W m) (-f) (-f) := by
    change 0 < ⟪shiftedOperator W m (Variation.directionToL2 (-f)),
      Variation.directionToL2 (-f)⟫
    change 0 < ⟪shiftedOperator W m (Variation.directionToL2 f),
      Variation.directionToL2 f⟫ at hq
    simpa only [map_neg, inner_neg_left, inner_neg_right, neg_neg] using hq
  have hβW : ContDiffAt ℝ 2 β (density W) := hW.density_eq ▸ hβ
  have hmW : m = deriv β (density W) := by simpa only [hW.density_eq] using hm
  have hsideW : β =ᶠ[nhdsWithin (density W) (Iic (density W))] benchmark :=
    hW.density_eq ▸ hside
  have hcurvature := full_side_curvature W hW.full hglobal β hβW (Iic (density W))
    hsideW m _ hW.stationary hmW (-f) (quadratic_density_left (by linarith))
  have hnonpos : deriv (deriv β) (density W) *
      (Variation.weightFirstVariation (adjacencyOperator W) (-f) / 2) ^ 2 ≤ 0 := by
    rw [hW.density_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hconcave (sq_nonneg _)
  exact (not_le_of_gt hpositive) (hcurvature.trans hnonpos)

end Erdos1017.CappedModel
