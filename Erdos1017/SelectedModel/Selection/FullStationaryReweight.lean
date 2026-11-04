module

public import Erdos1017.Models.Selection.FullStationaryCompactness
public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.SelectedModel.Selection.FullReweightRows
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Stationary class under small reweightings

Vanishing tangent and quadratic variations preserve density and objective under
same-kernel reweighting, the reweighted degree stays nonconstant near zero, and
every sufficiently small exact-density reweighting has its own regular
multiplier in the full stationary class on the changed law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Determinism of one shifted sampled color already fixes the original
present charge to its conditional mean, on the same displayed kernel. -/
theorem conditionalCharge_deterministic_of_shifted (W : Model Ω μ) (m : ℝ)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p,
      shiftedColor m z = shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z := by
  have hcomp := shifted_complementary_of_deterministic W m hdet
  filter_upwards [hdet, hcomp] with p hp hc
  by_cases hA : W.moment CappedColor.adjacency p = 0
  · filter_upwards [ae_adjacency_zero_of_moment_zero W p hA] with z hz
    have hlo := neg_three_adjacency_le_charge z
    have hhi := charge_le_adjacency z
    rw [hz] at hlo hhi
    have hy : CappedColor.charge z = 0 := by linarith
    rw [hy, hz, mul_zero]
  · by_cases hM : shiftedMoment W m p = 0
    · have hcond : conditionalCharge W p = m := by
        rw [shiftedMoment_eq_conditional] at hM
        exact sub_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hA)
      filter_upwards [hp] with z hz
      rw [shiftedColor, hM] at hz
      rw [hcond]
      exact sub_eq_zero.mp hz
    · have hAone : W.moment CappedColor.adjacency p = 1 := by
        have := (mul_eq_zero.mp hc).resolve_right hM
        linarith
      filter_upwards [hp, ae_adjacency_one_of_moment_one W p hAone] with z hz ha
      rw [shiftedColor, ha, shiftedMoment_eq, hAone] at hz
      simp only [conditionalCharge, hAone, div_one, ha, mul_one]
      linarith

omit [IsProbabilityMeasure μ] in
private theorem shiftedColor_deterministic_of_complementary_ae (W : Model Ω μ) (m : ℝ)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p,
      CappedColor.charge z = conditionalCharge W p * CappedColor.adjacency z) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p,
      shiftedColor m z = shiftedMoment W m p := by
  filter_upwards [hcomp, hdet] with p hp hdetp
  have hM := shiftedMoment_eq_conditional W m p
  by_cases hz : conditionalCharge W p - m = 0
  · have heq : conditionalCharge W p = m := sub_eq_zero.mp hz
    filter_upwards [hdetp] with z hc
    rw [shiftedColor, hc, heq, hM, hz, mul_zero, sub_self]
  · rw [hM] at hp
    have hprod : ((1 - W.moment CappedColor.adjacency p) *
        W.moment CappedColor.adjacency p) * (conditionalCharge W p - m) = 0 := by
      convert hp using 1
      ring
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hz) with hone | hzero
    · have hAone : W.moment CappedColor.adjacency p = 1 := by linarith
      filter_upwards [hdetp, ae_adjacency_one_of_moment_one W p hAone] with z hc ha
      rw [shiftedColor, hc, ha, hM, hAone]
      ring
    · filter_upwards [hdetp, ae_adjacency_zero_of_moment_zero W p hzero] with z hc ha
      rw [shiftedColor, hc, ha, hM, hzero]
      ring

/-- Vanishing tangent and quadratic variations preserve the original density
and objective exactly under the actual same-kernel reweighting. -/
theorem FullStationaryClass.reweight_density_objective {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (h : Variation.WeightDirections μ)
    (hfirst : Variation.weightFirstVariation (adjacencyOperator W) h = 0)
    (hA : Variation.weightSecondVariation (adjacencyOperator W) h h = 0)
    (hM : Variation.weightSecondVariation (shiftedOperator W m) h h = 0)
    (t : ℝ) (ht : ‖t • h‖ < 1) :
    density (reweight W (t • h) ht) = d ∧ objective (reweight W (t • h) ht) = c := by
  have hshift := shiftedFirstVariation_zero_of_stationary W m _ hW.stationary
  have hYfirst := LinearMap.congr_fun (firstVariation_identity_of_shifted_zero W m hshift) h
  simp only [LinearMap.smul_apply, smul_eq_mul, hfirst, mul_zero] at hYfirst
  have hY : Variation.weightSecondVariation (chargeOperator W) h h = 0 := by
    change ⟪shiftedOperator W m (Variation.directionToL2 h), Variation.directionToL2 h⟫ = 0 at hM
    rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left] at hM
    change ⟪adjacencyOperator W (Variation.directionToL2 h), Variation.directionToL2 h⟫ = 0 at hA
    change ⟪chargeOperator W (Variation.directionToL2 h), Variation.directionToL2 h⟫ = 0
    rw [hA, mul_zero, sub_zero] at hM
    exact hM
  constructor
  · rw [density_reweight_smul, hfirst, hA]
    simpa using hW.density_eq
  · rw [objective_reweight_smul, hYfirst, hY]
    simpa using hW.objective_eq

/-- A fixed old transverse mean-zero test keeps the reweighted original
degree nonconstant near zero, using equivalent measures and old L2 rows. -/
theorem eventually_reweight_degree_nonconstant (W : Model Ω μ)
    (h u : Variation.WeightDirections μ)
    (hu : Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0) :
    ∀ᶠ t : ℝ in nhds 0, ∀ ht : ‖t • h‖ < 1,
      ¬ ∃ a : ℝ, ∀ᵐ x ∂weightedMeasure (μ := μ) (Variation.vertexWeight (t • h)),
        (∫ y, adjacencyKernel (reweight W (t • h) ht) x y
          ∂weightedMeasure (μ := μ) (Variation.vertexWeight (t • h))) = a := by
  let D := fun t : ℝ => ⟪adjacencyOperator W (Variation.vertexWeight (t • h)),
    Variation.directionToL2 u⟫
  have hD : ContinuousAt D 0 := by
    dsimp only [D, Variation.vertexWeight]
    fun_prop
  have hD0 : D 0 ≠ 0 := by
    intro hz
    apply hu
    change 2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 u⟫ = 0
    simpa only [D, Variation.vertexWeight, zero_smul, map_zero, add_zero, hz, mul_zero] using
      congrArg (fun a : ℝ => 2 * a) hz
  have hnear : ∀ᶠ t : ℝ in nhds 0, D t ≠ 0 := hD.eventually (eventually_ne_nhds hD0)
  filter_upwards [hnear] with t ht htweight
  rintro ⟨a, hrow⟩
  have hrowold := adjacency_reweight_stationary_oldL2 W (t • h) htweight a hrow
  apply ht
  dsimp only [D]
  rw [hrowold, real_inner_smul_left, KernelOperator.inner_constant_one,
    Variation.direction_integral_zero, mul_zero]

variable [MeasurableSpace.CountablyGenerated Ω]

/-- Every sufficiently small exact-density reweighting has its own actual
regular multiplier in the full stationary class on the changed law. The
displayed kernel is retained and all new class properties are derived. -/
theorem FullStationaryClass.eventually_reweight {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (h u : Variation.WeightDirections μ)
    (hu : Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0)
    (hfirst : Variation.weightFirstVariation (adjacencyOperator W) h = 0)
    (hA : Variation.weightSecondVariation (adjacencyOperator W) h h = 0)
    (hM : Variation.weightSecondVariation (shiftedOperator W m) h h = 0) :
    ∀ᶠ t : ℝ in nhds 0, ∃ ht : ‖t • h‖ < 1,
      letI : IsProbabilityMeasure
          (weightedMeasure (μ := μ) (Variation.vertexWeight (t • h))) :=
        weightedMeasure_probability
          ((Lp.memLp (Variation.vertexWeight (t • h))).integrable (by norm_num))
          (Variation.vertexWeight_nonnegative (t • h) ht)
          (Variation.vertexWeight_integral (t • h))
      ∃ n : ℝ, FullStationaryClass d c (reweight W (t • h) ht) n ∧
        shiftedOperator W n (Variation.vertexWeight (t • h)) =
          (2 * (c - n * d)) • Lp.const 2 μ (1 : ℝ) := by
  have hnorm : ContinuousAt (fun t : ℝ => ‖t • h‖) 0 := by fun_prop
  have hsmall : ∀ᶠ t : ℝ in nhds 0, ‖t • h‖ < 1 :=
    hnorm.eventually (eventually_lt_nhds (by simp))
  have hnonconstant := eventually_reweight_degree_nonconstant W h u hu
  filter_upwards [hsmall, hnonconstant] with t ht hdegree
  refine ⟨ht, ?_⟩
  let ν := weightedMeasure (μ := μ) (Variation.vertexWeight (t • h))
  have hprob : IsProbabilityMeasure ν := weightedMeasure_probability
    ((Lp.memLp (Variation.vertexWeight (t • h))).integrable (by norm_num))
    (Variation.vertexWeight_nonnegative (t • h) ht) (Variation.vertexWeight_integral (t • h))
  have : IsProbabilityMeasure ν := hprob
  have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℝ 2 ν) := inferInstance
  let U : Model Ω ν := reweight W (t • h) ht
  have hfull : FullFeasible U := fullFeasible_reweight W hW.full (t • h) ht
  obtain ⟨hdU, hcU⟩ := hW.reweight_density_objective h hfirst hA hM t ht
  have hopt : objective U = FractionalGraph.densityLimit (density U) := by
    rw [hcU, hdU]
    exact hW.optimal
  have hregular : Variation.weightFirstVariation (adjacencyOperator U) ≠ 0 := by
    intro hz
    apply hdegree ht
    exact (Variation.kernel_weightFirstVariation_eq_zero_iff (adjacencyKernel U)
      (by norm_num) (adjacencyKernel_measurable U) (adjacencyKernel_bound U)).mp hz
  obtain ⟨n, a, hn, _, _, hmem, hcomp, hrow, ha, hfinite, hindex⟩ :=
    exists_full_regular_kernel U hfull hopt hregular
      (by rw [hdU]; exact hd.1) (by rw [hdU]; exact hd.2)
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hconditional : ∀ᵐ p ∂ν.prod ν, ∀ᵐ z ∂U.kernel p,
      CappedColor.charge z = conditionalCharge U p * CappedColor.adjacency z := by
    exact (hac.prod hac).ae_le (conditionalCharge_deterministic_of_shifted W m hW.deterministic)
  have hdet := shiftedColor_deterministic_of_complementary_ae U n hcomp hconditional
  have hrow' : ∀ᵐ x ∂ν, (∫ y, shiftedKernel U n x y ∂ν) = 2 * (c - n * d) := by
    rw [ha, hcU, hdU] at hrow
    exact hrow
  have hclass : FullStationaryClass d c U n :=
    ⟨hfull, hdU, hcU, hW.optimal, hn, hdet, hmem, hcomp, hrow', hfinite, hindex⟩
  exact ⟨n, hclass, shifted_reweight_stationary_oldL2 W (t • h) ht n _ hrow'⟩

end Erdos1017.CappedModel
