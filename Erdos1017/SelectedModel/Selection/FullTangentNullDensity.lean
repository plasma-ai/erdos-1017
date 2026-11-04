module

public import Erdos1017.SelectedModel.Selection.FullNullDirectionRigidity
public import Erdos1017.SelectedModel.Selection.QuadraticTangentNullCorrection

/-!
# Zero adjacency energy of tangent null directions

At the full optimum, a degree-tangent bounded direction with zero shifted energy
has vanishing adjacency quadratic energy, with transversality supplied by the
regular tangent inequality or a positive eigenvector, and the result extends to
bounded `L²` classes tangent to mass and degree.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- At the actual full optimum, zero shifted energy in a degree-tangent
bounded direction forces its adjacency quadratic energy to vanish. The
exact density correction and its mixed shifted term are constructed. -/
theorem full_tangent_null_density_of_transverse
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Variation.WeightDirections μ)
    (hdegree : Variation.weightFirstVariation (adjacencyOperator W) f = 0)
    (henergy : Variation.weightSecondVariation (shiftedOperator W m) f f = 0) :
    Variation.weightSecondVariation (adjacencyOperator W) f f = 0 := by
  let A := adjacencyOperator W
  let M := shiftedOperator W m
  let one := Lp.const 2 μ (1 : ℝ)
  let ε := 1 / (‖f‖ + ‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεeq : ε * (‖f‖ + ‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity)
  have hMsym : M.toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric _ _ _ _
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  apply Variation.tangent_null_density_coefficient_eq_zero
    (Variation.weightSecondVariation A f f) (Variation.weightFirstVariation A u)
    (Variation.weightSecondVariation A f u) (Variation.weightSecondVariation A u u)
    (Variation.weightSecondVariation M f u) (Variation.weightSecondVariation M u u)
    hu hq ε hε
  intro t s ht hs hroot
  let v := t • f + s • u
  have hnorm : ‖v‖ < 1 := by
    have hn := norm_add_le (t • f) (s • u)
    simp only [norm_smul, Real.norm_eq_abs] at hn
    have hfbound := mul_le_mul_of_nonneg_right ht.le (norm_nonneg f)
    have hubound := mul_le_mul_of_nonneg_right hs.le (norm_nonneg u)
    dsimp only [v]
    nlinarith
  have hden : ⟪A (Variation.vertexWeight v), Variation.vertexWeight v⟫ = ⟪A one, one⟫ := by
    rw [Variation.vertexWeight, Variation.weighted_quadratic_expansion A
      (adjacencyOperator_symmetric W)]
    have hquad : Variation.weightFirstVariation A v +
        Variation.weightSecondVariation A v v =
        Variation.weightSecondVariation A f f * t ^ 2 +
          (Variation.weightFirstVariation A u + 2 * Variation.weightSecondVariation A f u * t) * s +
            Variation.weightSecondVariation A u u * s ^ 2 := by
      dsimp only [v]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [Variation.weightSecondVariation_symm A (adjacencyOperator_symmetric W) u f,
        hdegree]
      ring
    rw [add_assoc, hquad, hroot, add_zero]
  have hdenPair : Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight v) =
      Variation.weightedPairIntegral (adjacencyKernel W) one := by
    simpa only [weighted_adjacency_eq] using hden
  have hcharge := full_weight_local_max W hW hopt v hnorm hdenPair
  rw [weighted_charge_eq, weighted_charge_eq] at hcharge
  have hshift : ⟪M (Variation.vertexWeight v), Variation.vertexWeight v⟫ - ⟪M one, one⟫ ≤ 0 := by
    dsimp only [M]
    rw [shiftedOperator_eq]
    simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
    change ⟪chargeOperator W (Variation.vertexWeight v), Variation.vertexWeight v⟫ -
        m * ⟪A (Variation.vertexWeight v), Variation.vertexWeight v⟫ -
        (⟪chargeOperator W one, one⟫ - m * ⟪A one, one⟫) ≤ 0
    rw [hden]
    linarith
  have hcost := Variation.weighted_quadratic_expansion M hMsym v
  change _ = ⟪M one, one⟫ + _ + _ at hcost
  rw [hfirst, LinearMap.zero_apply, add_zero] at hcost
  have hquad : Variation.weightSecondVariation M v v =
      2 * Variation.weightSecondVariation M f u * t * s +
        Variation.weightSecondVariation M u u * s ^ 2 := by
    dsimp only [v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Variation.weightSecondVariation_symm M hMsym u f, henergy]
    ring
  rw [hquad] at hcost
  change ⟪M (Variation.vertexWeight v), Variation.vertexWeight v⟫ =
    ⟪M one, one⟫ + (2 * Variation.weightSecondVariation M f u * t * s +
      Variation.weightSecondVariation M u u * s ^ 2) at hcost
  linarith

/-- The same full optimum's regular tangent inequality supplies
transversality of its positive direction and determines a usable sign. -/
theorem full_tangent_null_density
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Variation.WeightDirections μ)
    (hdegree : Variation.weightFirstVariation (adjacencyOperator W) f = 0)
    (henergy : Variation.weightSecondVariation (shiftedOperator W m) f f = 0) :
    Variation.weightSecondVariation (adjacencyOperator W) f f = 0 := by
  have hu := full_positive_direction_transverse W hW hopt m hfirst hregular u hq
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · apply full_tangent_null_density_of_transverse W hW hopt m hfirst (-u)
      (by simpa only [map_neg] using neg_pos.mpr hneg) _ f hdegree henergy
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hq
  · exact full_tangent_null_density_of_transverse W hW hopt m hfirst u hpos hq f hdegree henergy

/-- Every bounded L² class tangent to mass and degree, with zero shifted
energy, has zero adjacency energy at the same stationary full optimum. -/
theorem full_tangent_null_vector_density
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0)
    (henergy : ⟪shiftedOperator W m f, f⟫ = 0) :
    ⟪adjacencyOperator W f, f⟫ = 0 := by
  obtain ⟨g, hg⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  have hgdegree : Variation.weightFirstVariation (adjacencyOperator W) g = 0 := by
    change 2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 g⟫ = 0
    rw [hg, hdegree, mul_zero]
  have hgenergy : Variation.weightSecondVariation (shiftedOperator W m) g g = 0 := by
    change ⟪shiftedOperator W m (Variation.directionToL2 g), Variation.directionToL2 g⟫ = 0
    rwa [hg]
  have h := full_tangent_null_density W hW hopt m hfirst hregular u hq g hgdegree hgenergy
  change ⟪adjacencyOperator W (Variation.directionToL2 g), Variation.directionToL2 g⟫ = 0 at h
  rwa [hg] at h

/-- The supplied positive eigenvector yields its bounded transverse
direction internally; no kernel-null or selected-multiplier premise is used. -/
theorem full_tangent_null_vector_density_of_positive_eigenvector
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hwmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (heigen : shiftedOperator W m w = σ • w)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hmean : (∫ x, f x ∂μ) = 0)
    (hdegree : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0)
    (henergy : ⟪shiftedOperator W m f, f⟫ = 0) :
    ⟪adjacencyOperator W f, f⟫ = 0 := by
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hwmean σ hσ heigen
  exact full_tangent_null_vector_density W hW hopt m ν hrow hregular u hq
    f hf hmean hdegree henergy

end Erdos1017.CappedModel
