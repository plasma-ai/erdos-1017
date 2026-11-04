module

public import Erdos1017.SelectedModel.Selection.FullPositiveEigenvector
public import Erdos1017.SelectedModel.Selection.QuadraticNullCorrection

/-!
# Rigidity of null directions at a full optimum

Every bounded null vector of the stationary full optimum has zero mean and zero
first and second adjacency variations, using an exact density correction and a
transverse sign from regular adjacency or a positive mean-zero eigenvector.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The small bounded weight changes used in the correction have strictly
positive probability densities almost everywhere. -/
theorem vertexWeight_positive (f : WeightDirections μ) (hf : ‖f‖ < 1) :
    ∀ᵐ x ∂μ, 0 < vertexWeight f x := by
  filter_upwards [Lp.coeFn_add (Lp.const 2 μ (1 : ℝ)) (directionToL2 f),
    Lp.coeFn_const 2 μ (1 : ℝ), bounded_ae_norm_le f.val] with x ha hc hb
  change 0 < (Lp.const 2 μ (1 : ℝ) + directionToL2 f) x
  rw [ha]
  change 0 < (Lp.const 2 μ (1 : ℝ)) x + directionToL2 f x
  rw [hc]
  change 0 < 1 + directionToL2 f x
  change ‖directionToL2 f x‖ ≤ ‖f‖ at hb
  rw [Real.norm_eq_abs] at hb
  linarith [neg_abs_le (directionToL2 f x)]

end Erdos1017.Variation

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem shiftedOperator_symmetric (W : Model Ω μ) (m : ℝ) :
    (shiftedOperator W m).toLinearMap.IsSymmetric := by
  apply KernelOperator.operator_symmetric _ _ _ _
  filter_upwards [shiftedMoment_symm W m] with p hp
  exact hp.symm

/-- Actual full-model optimality and an internally constructed exact density
correction force both adjacency variations of a bounded null direction to
vanish. The supplied transverse direction has positive first variation. -/
theorem full_null_direction_density_rigidity_of_transverse
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (u : Variation.WeightDirections μ)
    (hu : 0 < Variation.weightFirstVariation (adjacencyOperator W) u)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Variation.WeightDirections μ)
    (hnull : shiftedOperator W m (Variation.directionToL2 f) = 0) :
    Variation.weightFirstVariation (adjacencyOperator W) f = 0 ∧
      Variation.weightSecondVariation (adjacencyOperator W) f f = 0 := by
  let A := adjacencyOperator W
  let M := shiftedOperator W m
  let one := Lp.const 2 μ (1 : ℝ)
  let ε := 1 / (‖f‖ + ‖u‖ + 1)
  have hε : 0 < ε := div_pos (by norm_num) (by positivity)
  have hεeq : ε * (‖f‖ + ‖u‖ + 1) = 1 := div_mul_cancel₀ _ (by positivity)
  have hMsym := shiftedOperator_symmetric W m
  have hMff : Variation.weightSecondVariation M f f = 0 := by
    change ⟪shiftedOperator W m (Variation.directionToL2 f), Variation.directionToL2 f⟫ = 0
    rw [hnull, inner_zero_left]
  have hMfu : Variation.weightSecondVariation M f u = 0 := by
    change ⟪shiftedOperator W m (Variation.directionToL2 f), Variation.directionToL2 u⟫ = 0
    rw [hnull, inner_zero_left]
  have hMuf : Variation.weightSecondVariation M u f = 0 := by
    rw [Variation.weightSecondVariation_symm M hMsym, hMfu]
  apply Variation.null_density_coefficients_eq_zero
    (Variation.weightFirstVariation A f) (Variation.weightSecondVariation A f f)
    (Variation.weightFirstVariation A u) (Variation.weightSecondVariation A f u)
    (Variation.weightSecondVariation A u u) (Variation.weightSecondVariation M u u)
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
        Variation.weightFirstVariation A f * t + Variation.weightSecondVariation A f f * t ^ 2 +
          (Variation.weightFirstVariation A u + 2 * Variation.weightSecondVariation A f u * t) * s +
            Variation.weightSecondVariation A u u * s ^ 2 := by
      dsimp only [v]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [Variation.weightSecondVariation_symm A (adjacencyOperator_symmetric W) u f]
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
      Variation.weightSecondVariation M u u * s ^ 2 := by
    dsimp only [v]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hMff, hMfu, hMuf]
    ring
  rw [hquad] at hcost
  change ⟪M (Variation.vertexWeight v), Variation.vertexWeight v⟫ =
    ⟪M one, one⟫ + Variation.weightSecondVariation M u u * s ^ 2 at hcost
  linarith

/-- Regular adjacency and a positive shifted direction determine a usable
transverse sign from the same actual full optimum. -/
theorem full_null_direction_density_rigidity
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m : ℝ) (hfirst : Variation.weightFirstVariation (shiftedOperator W m) = 0)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Variation.WeightDirections μ)
    (hnull : shiftedOperator W m (Variation.directionToL2 f) = 0) :
    Variation.weightFirstVariation (adjacencyOperator W) f = 0 ∧
      Variation.weightSecondVariation (adjacencyOperator W) f f = 0 := by
  have hu := full_positive_direction_transverse W hW hopt m hfirst hregular u hq
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · apply full_null_direction_density_rigidity_of_transverse W hW hopt m hfirst (-u)
      (by simpa only [map_neg] using neg_pos.mpr hneg) _ f hnull
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hq
  · exact full_null_direction_density_rigidity_of_transverse W hW hopt m hfirst u hpos hq f hnull

/-- A stationary shifted row with positive eigenvalue makes every actual
null vector mean zero. No null-mean identity is supplied by the caller. -/
theorem full_null_vector_mean_zero (W : Model Ω μ) (m ν : ℝ) (hν : 0 < ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (f : Lp ℝ 2 μ) (hnull : shiftedOperator W m f = 0) :
    (∫ x, f x ∂μ) = 0 := by
  have hstationary := KernelOperator.constant_one_eigenvector_of_stationary
    (shiftedKernel W m) (by positivity) (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) ν hrow
  have hsym := shiftedOperator_symmetric W m
  have hinner : ν * ⟪Lp.const 2 μ (1 : ℝ), f⟫ = 0 := by
    have heq := hsym (Lp.const 2 μ (1 : ℝ)) f
    change ⟪shiftedOperator W m (Lp.const 2 μ (1 : ℝ)), f⟫ =
      ⟪Lp.const 2 μ (1 : ℝ), shiftedOperator W m f⟫ at heq
    change shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) = _ at hstationary
    rw [hstationary, hnull, real_inner_smul_left, inner_zero_right] at heq
    exact heq
  rw [KernelOperator.inner_constant_one] at hinner
  exact (mul_eq_zero.mp hinner).resolve_left hν.ne'

/-- Every bounded null vector of the actual stationary full optimum has
zero mean and zero first and second adjacency variations. -/
theorem full_null_vector_density_rigidity
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hν : 0 < ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (u : Variation.WeightDirections μ)
    (hq : 0 < Variation.weightSecondVariation (shiftedOperator W m) u u)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hnull : shiftedOperator W m f = 0) :
    (∫ x, f x ∂μ) = 0 ∧
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0 ∧
      ⟪adjacencyOperator W f, f⟫ = 0 := by
  have hmean := full_null_vector_mean_zero W m ν hν hrow f hnull
  obtain ⟨g, hg⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
  have hfirst := shiftedFirstVariation_zero_of_stationary W m ν hrow
  have hrigid := full_null_direction_density_rigidity W hW hopt m hfirst hregular u hq g
    (by rwa [hg])
  refine ⟨hmean, ?_, ?_⟩
  · have hlinear := hrigid.1
    change 2 * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Variation.directionToL2 g⟫ = 0
      at hlinear
    rw [hg] at hlinear
    linarith
  · have hquad := hrigid.2
    change ⟪adjacencyOperator W (Variation.directionToL2 g), Variation.directionToL2 g⟫ = 0
      at hquad
    rwa [hg] at hquad

/-- An actual positive mean-zero eigenvector supplies its bounded transverse
direction internally. Both adjacency null identities then follow for every
bounded null vector of the same full optimum. -/
theorem full_null_vector_density_rigidity_of_positive_eigenvector
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hν : 0 < ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (w : Lp ℝ 2 μ) (hw : w ≠ 0) (hmean : (∫ x, w x ∂μ) = 0)
    (σ : ℝ) (hσ : 0 < σ) (heigen : shiftedOperator W m w = σ • w)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hnull : shiftedOperator W m f = 0) :
    (∫ x, f x ∂μ) = 0 ∧
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ = 0 ∧
      ⟪adjacencyOperator W f, f⟫ = 0 := by
  obtain ⟨u, hq⟩ := exists_positive_direction_of_eigenvector W m w hw hmean σ hσ heigen
  exact full_null_vector_density_rigidity W hW hopt m ν hν hrow hregular u hq f hf hnull

end Erdos1017.CappedModel
