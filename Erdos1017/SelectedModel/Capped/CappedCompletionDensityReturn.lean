module

public import Erdos1017.SelectedModel.Capped.CappedZeroCompletion
public import Erdos1017.SelectedModel.Flows.CompletionDensityReturn
public import Erdos1017.SelectedModel.Selection.FullSmoothContact
public import Erdos1017.Models.Selection.FullModelEdits

/-!
# No missing mass at a full optimum with a positive direction

All-order completed scalar tests rule out positive missing mass at a full
optimum that has a transverse positive shifted direction
(`missingMass_eq_zero_of_full_optimum`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace Topology

namespace Erdos1017.CappedModel.ZeroCompletion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem weightedPairIntegral_affine
    (K K₀ K₁ : Ω → Ω → ℝ) (c : ℝ)
    {B₀ B₁ : ℝ} (hK₀ : AEStronglyMeasurable
      (fun p : Ω × Ω => K₀ p.1 p.2) (μ.prod μ))
    (hB₀ : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K₀ p.1 p.2‖ ≤ B₀)
    (hK₁ : AEStronglyMeasurable
      (fun p : Ω × Ω => K₁ p.1 p.2) (μ.prod μ))
    (hB₁ : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K₁ p.1 p.2‖ ≤ B₁)
    (hEq : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      K p.1 p.2 = K₀ p.1 p.2 + c * K₁ p.1 p.2)
    (f : Lp ℝ 2 μ) :
    Variation.weightedPairIntegral K f =
      Variation.weightedPairIntegral K₀ f +
        c * Variation.weightedPairIntegral K₁ f := by
  have hInt₀ := KernelOperator.integrable_bilinear hK₀ hB₀ f f
  have hInt₁ := KernelOperator.integrable_bilinear hK₁ hB₁ f f
  unfold Variation.weightedPairIntegral
  calc
    (∫ p : Ω × Ω, K p.1 p.2 * f p.2 * f p.1 ∂μ.prod μ) =
        ∫ p : Ω × Ω,
          K₀ p.1 p.2 * f p.2 * f p.1 +
            c * (K₁ p.1 p.2 * f p.2 * f p.1) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [hEq] with p hp
      rw [hp]
      ring
    _ = _ := by
      rw [integral_add hInt₀ (hInt₁.const_mul c), integral_const_mul]

private theorem missing_weight_continuous
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (u : Variation.WeightDirections μ) :
    Continuous (fun s : ℝ =>
      ⟪T (Variation.vertexWeight (s • u)), Variation.vertexWeight (s • u)⟫ / 2) := by
  have hv : Continuous (fun s : ℝ => Variation.vertexWeight (s • u)) := by
    simp only [Variation.vertexWeight, map_smul]
    fun_prop
  exact ((T.continuous.comp hv).inner hv).div_const 2

/-- Actual all-order completed scalar tests rule out positive missing mass
at a full optimum with a transverse positive shifted direction. The density
return uses the original shifted kernel and an actual reweighted completion. -/
theorem missingMass_eq_zero_of_full_optimum
    (W : Model Ω μ)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (u : Variation.WeightDirections μ)
    (hL : Variation.weightFirstVariation (adjacencyOperator W) u ≠ 0)
    (hQ : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (D : Set Ω) [DecidablePred (· ∈ D)] (hD : MeasurableSet D)
    (hcap : ∀ n, 2 ≤ n → FiniteArity.FeasibleOrder μ
      (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D)
      (FiniteArity.completeCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) D (-m)) n) :
    missingMass W m D = 0 := by
  by_contra hzero
  have hpositive : 0 < missingMass W m D := by
    by_contra hnot
    exact hzero (le_antisymm (le_of_not_gt hnot) (missingMass_nonneg W m D))
  let K : Ω → Ω → ℝ := fun x y => missing W m D (x, y)
  have hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ) := by
    simpa only [K] using (measurable_missing W m D hD).aestronglyMeasurable
  have hB : ∀ᵐ p : Ω × Ω ∂μ.prod μ, ‖K p.1 p.2‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    change ‖missing W m D p‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (missing_mem W m D p).1]
    exact (missing_mem W m D p).2
  let T := KernelOperator.operator K (by norm_num : (0 : ℝ) ≤ 1) hK hB
  let Z : ℝ → ℝ := fun s =>
    ⟪T (Variation.vertexWeight (s • u)), Variation.vertexWeight (s • u)⟫ / 2
  have hZweighted (s : ℝ) : Z s =
      Variation.weightedPairIntegral K (Variation.vertexWeight (s • u)) / 2 := by
    dsimp only [Z, T]
    rw [Variation.weightedPairIntegral_eq K (by norm_num) hK hB]
  have hZcontinuous : ContinuousAt Z 0 := (missing_weight_continuous T u).continuousAt
  have hZzero : Z 0 = missingMass W m D := by
    rw [hZweighted]
    simp only [zero_smul, Variation.vertexWeight, map_zero, add_zero]
    rw [weightedPairIntegral_one]
    rfl
  let L := Variation.weightFirstVariation (adjacencyOperator W) u / 2
  let qGraph := Variation.weightSecondVariation (adjacencyOperator W) u u / 2
  let qShift := Variation.weightSecondVariation (shiftedOperator W m) u u / 2
  have hLnonzero : L ≠ 0 := div_ne_zero hL (by norm_num)
  have hqpositive : 0 < qShift := div_pos hQ (by norm_num)
  let ε := 1 / (‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  obtain ⟨s, t, hsε, ht, _, _, _, hreturn, hgain⟩ :=
    CompletionDensityReturn.exists_small_exact_density_return L qGraph qShift Z
      hLnonzero hZcontinuous (hZzero ▸ hpositive) hqpositive ε hε
  let τ : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
  have hnorm : ‖s • u‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hεeq : ε * (‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hsε.le (norm_nonneg u)
    have hpos := mul_pos hε (by norm_num : (0 : ℝ) < 1)
    nlinarith
  have : IsProbabilityMeasure
      (weightedMeasure (μ := μ) (Variation.vertexWeight (s • u))) :=
    weightedMeasure_probability
      ((Lp.memLp (Variation.vertexWeight (s • u))).integrable (by norm_num))
      (Variation.vertexWeight_nonnegative (s • u) hnorm)
      (Variation.vertexWeight_integral (s • u))
  let V := model W m D hD hm τ
  have hAdj (f : Lp ℝ 2 μ) :
      Variation.weightedPairIntegral (adjacencyKernel V) f =
        Variation.weightedPairIntegral (adjacencyKernel W) f +
          t * Variation.weightedPairIntegral K f := by
    apply weightedPairIntegral_affine _ _ _ t
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W) hK hB
    filter_upwards [adjacency_moment_ae_eq W m D hD hm hsupport τ] with p hp
    simpa only [V, adjacencyKernel, K] using hp
  have hCharge (f : Lp ℝ 2 μ) :
      Variation.weightedPairIntegral (chargeKernel V) f =
        Variation.weightedPairIntegral (chargeKernel W) f +
          (m * t) * Variation.weightedPairIntegral K f := by
    apply weightedPairIntegral_affine _ _ _ (m * t)
      (chargeKernel_measurable W) (chargeKernel_bound W) hK hB
    filter_upwards [charge_moment_ae_eq W m D hD hm hsupport τ] with p hp
    simpa only [V, chargeKernel, K] using hp
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  have hfirstEq := LinearMap.congr_fun (firstVariation_identity_of_shifted_zero W m hfirst) u
  simp only [LinearMap.smul_apply, smul_eq_mul] at hfirstEq
  have hsecondEq : Variation.weightSecondVariation (shiftedOperator W m) u u =
      Variation.weightSecondVariation (chargeOperator W) u u -
        m * Variation.weightSecondVariation (adjacencyOperator W) u u := by
    change ⟪shiftedOperator W m (Variation.directionToL2 u),
      Variation.directionToL2 u⟫ = _
    rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
    rfl
  have hdensity : density (reweight V (s • u) hnorm) =
      density W + L * s + qGraph * s ^ 2 + t * Z s := by
    calc
      density (reweight V (s • u) hnorm) =
          (Variation.weightedPairIntegral (adjacencyKernel W)
            (Variation.vertexWeight (s • u)) +
            t * Variation.weightedPairIntegral K (Variation.vertexWeight (s • u))) / 2 := by
        rw [density_reweight]
        change Variation.weightedPairIntegral (adjacencyKernel V)
          (Variation.vertexWeight (s • u)) / 2 = _
        rw [hAdj]
      _ = density (reweight W (s • u) hnorm) + t * Z s := by
        rw [density_reweight W (s • u) hnorm, hZweighted]
        unfold adjacencyKernel
        ring
      _ = density W + L * s + qGraph * s ^ 2 + t * Z s := by
        rw [density_reweight_smul]
        dsimp only [L, qGraph]
        ring
  have hobjective : objective (reweight V (s • u) hnorm) =
      objective W + m * (L * s + qGraph * s ^ 2 + t * Z s) + qShift * s ^ 2 := by
    calc
      objective (reweight V (s • u) hnorm) =
          (Variation.weightedPairIntegral (chargeKernel W)
            (Variation.vertexWeight (s • u)) +
            (m * t) * Variation.weightedPairIntegral K (Variation.vertexWeight (s • u))) / 2 := by
        rw [objective_reweight]
        change Variation.weightedPairIntegral (chargeKernel V)
          (Variation.vertexWeight (s • u)) / 2 = _
        rw [hCharge]
      _ = objective (reweight W (s • u) hnorm) + m * t * Z s := by
        rw [objective_reweight W (s • u) hnorm, hZweighted]
        unfold chargeKernel
        ring
      _ = objective W + m * (L * s + qGraph * s ^ 2 + t * Z s) + qShift * s ^ 2 := by
        rw [objective_reweight_smul]
        dsimp only [L, qGraph, qShift]
        have hsecondCharge : Variation.weightSecondVariation (chargeOperator W) u u =
            Variation.weightSecondVariation (shiftedOperator W m) u u +
              m * Variation.weightSecondVariation (adjacencyOperator W) u u := by
          linear_combination -hsecondEq
        rw [hfirstEq, hsecondCharge]
        ring
  have hfull : FullFeasible V := fullFeasible_model W m D hD hm hcap τ
  have hfeasible : FullFeasible (reweight V (s • u) hnorm) :=
    fullFeasible_reweight V hfull (s • u) hnorm
  have hdensityEq : density (reweight V (s • u) hnorm) = density W := by
    rw [hdensity]
    linarith
  have hbound := full_objective_le_of_density_eq W hopt _
    (reweight V (s • u) hnorm) hfeasible hdensityEq
  have hgainExact : objective (reweight V (s • u) hnorm) =
      objective W + qShift * s ^ 2 := by
    rw [hobjective, hreturn]
    ring
  rw [hgainExact] at hbound
  linarith [hgain]

end Erdos1017.CappedModel.ZeroCompletion
