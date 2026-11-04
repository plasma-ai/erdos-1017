module

public import Erdos1017.Exclusions.SmoothW.FreshIndependentStarValues
public import Erdos1017.Exclusions.Common.CopyWeightExpansion
public import Erdos1017.Exclusions.Common.CopyMassCorrection
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Fresh-star mass cap for independent sets

An independent set obeys the original optimum's fresh-star mass cap, with all
scalar clique tests and the exact-density return constructed from the same
original model (`independent_set_mass_le_stationary`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual independent set obeys the original optimum's fresh-star
mass cap. All scalar clique tests and the exact-density return are
constructed from the same original model. -/
theorem FullStationaryClass.independent_set_mass_le_stationary
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (D : Set Ω) (hD : MeasurableSet D)
    (hind : ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ D → p.2 ∈ D → adjacencyKernel W p.1 p.2 = 0) :
    (1 - m) * μ.real D ≤ 2 * (c - m * d) := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let f := D.indicator (fun _ => (1 : ℝ))
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hbound := PhysicalRepresentative.charge_bound W m
  have hYzero := PhysicalRepresentative.charge_zero_of_nonedge W m
  have hstructure := hW.strict_gap_structure hd hgap
  have hindependent : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → A p.1 p.2 = false := by
    filter_upwards [hind, PhysicalRepresentative.adjacency_moment_ae_eq W m
      hstructure.strict_support] with p hp he hx hy
    have hz := hp hx hy
    change W.moment CappedColor.adjacency p = 0 at hz
    change W.moment CappedColor.adjacency p = (if A p.1 p.2 = true then 1 else 0) at he
    exact Bool.eq_false_iff.mpr (fun ha => by simp [ha, hz] at he)
  have hcomparison := FreshIndependentStar.objective_le_densityLimit_ac
    A (PhysicalRepresentative.adjacency_symm W m) hA Y hY
    (PhysicalRepresentative.charge_symm W m) D hD 3 (by norm_num) hbound hYzero hindependent
    (PhysicalRepresentative.full_feasible W hW.full m hstructure.strict_support hW.deterministic)
  obtain ⟨u, hu⟩ : ∃ u : Variation.WeightDirections μ,
      0 < Variation.weightFirstVariation (adjacencyOperator W) u := by
    have hex : ∃ u, Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0 := by
      by_contra h
      push Not at h
      exact hstructure.regular (LinearMap.ext h)
    obtain ⟨u, hu⟩ := hex
    rcases lt_or_gt_of_ne hu with hu | hu
    · exact ⟨-u, by simpa using neg_pos.mpr hu⟩
    · exact ⟨u, hu⟩
  have hm := firstVariation_identity_of_shifted_zero W m
    (shiftedFirstVariation_zero_of_stationary W m (2 * (c - m * d)) hW.stationary)
  have hmfirst := LinearMap.congr_fun hm u
  simp only [LinearMap.smul_apply, smul_eq_mul] at hmfirst
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity)
  have hf : StronglyMeasurable f := (measurable_const.indicator hD).stronglyMeasurable
  have hfbound : ∀ z, ‖f z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ D <;> simp [f, hz]
  let a := (∫ z, f z ∂μ) - 2 * d
  let b := Variation.weightFirstVariation (adjacencyOperator W) u / 2
  let b₂ := Variation.weightSecondVariation (adjacencyOperator W) u u / 2
  let a₁ := ∫ z, f z * Variation.directionToL2 u z ∂μ
  let C := (∫ z, f z ∂μ) - 2 * c
  let B := Variation.weightFirstVariation (chargeOperator W) u / 2
  let B₂ := Variation.weightSecondVariation (chargeOperator W) u u / 2
  have hsign : C - m * a ≤ 0 := by
    apply Variation.copy_mass_sign_of_local_max a (-d) b a₁ b₂ C (-c) B a₁ B₂ m
      (by dsimp only [b]; linarith) (by dsimp only [B, b]; linarith) ε hε
    intro τ s hτ hτε hs hroot
    have hnorm : ‖s • u‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hmul := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
      nlinarith [norm_nonneg u]
    let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))
    let : IsProbabilityMeasure ν := weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative _ hnorm) (Variation.vertexWeight_integral _)
    have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
    have hden := FreshIndependentStar.density_marked_mass (μ := ν) A hA D hD τ hτ
    have hcost := FreshIndependentStar.objective_marked_mass (μ := ν)
      Y hY D hD 3 hbound τ hτ
    have hdold := physicalDensity_vertexWeight_curve W m hstructure.strict_support u s hnorm
    have hcold := physicalObjective_vertexWeight_curve W m hstructure.strict_support u s hnorm
    have hfrow := integral_vertexWeight_curve u s hnorm f hf 1 hfbound
    rw [hW.density_eq] at hdold
    rw [hW.objective_eq] at hcold
    change FiniteCappedSamplingCost.physicalDensity ν A = _ at hdold
    change FiniteCappedSamplingCost.physicalObjective ν Y = _ at hcold
    change (∫ z, f z ∂ν) = _ at hfrow
    change FiniteCappedSamplingCost.physicalDensity _ _ =
      (FiniteCappedSamplingCost.physicalDensity ν A + τ * ∫ z, f z ∂ν) / (1 + τ) ^ 2 at hden
    change FiniteCappedSamplingCost.physicalObjective _ _ =
      (FiniteCappedSamplingCost.physicalObjective ν Y + τ * ∫ z, f z ∂ν) / (1 + τ) ^ 2 at hcost
    rw [hdold, hfrow] at hden
    rw [hcold, hfrow] at hcost
    have hdeneq : FiniteCappedSamplingCost.physicalDensity
        (universalMeasure ν (universalFraction τ hτ))
        (FreshIndependentStar.adjacency A D) = d := by
      rw [hden]
      apply (div_eq_iff (by positivity : (1 + τ) ^ 2 ≠ 0)).mpr
      dsimp only [a, b, b₂, a₁] at hroot
      nlinarith only [hroot]
    have hmax := hcomparison ν hac (universalFraction τ hτ)
    rw [hdeneq, ← hW.optimal, hcost] at hmax
    have hmul := (div_le_iff₀ (by positivity : 0 < (1 + τ) ^ 2)).mp hmax
    dsimp only [C, B, B₂, a₁]
    nlinarith only [hmul]
  have hmass : (∫ z, f z ∂μ) = μ.real D := by
    rw [show f = D.indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator hD, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
  dsimp only [C, a] at hsign
  rw [hmass] at hsign
  linarith

end Erdos1017.CappedModel
