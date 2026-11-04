module

public import Erdos1017.Models.Capped.CappedSingularMixedVariation
public import Erdos1017.Models.Capped.CappedEdgeSignConsequences
public import Erdos1017.Models.Capped.CappedRegularKernel

/-!
# The singular kernel of a capped optimizer

Separation over the common-envelope endpoints gives one singular multiplier for
every vertex and every such edit, and the singular capped branch has the same
kernel signs as the regular branch with the stronger positive-index bound one
(`exists_singular_kernel`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Separation over the family of all actual common-envelope endpoints
gives one singular multiplier for every vertex and every such edit. -/
theorem exists_singular_common_multiplier (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0) :
    ∃ m : ℝ, -3 ≤ m ∧ m ≤ 3 ∧
      (∀ f : Variation.WeightDirections μ,
        Variation.weightSecondVariation (chargeOperator W) f f -
          m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) ∧
      HasEditSigns W m := by
  let endpoints := {V : Model Ω μ // ∀ p, V.kernel p ≪ (editEnvelope W).kernel p}
  obtain ⟨m, hlo, hhi, hweight, hedit⟩ := exists_singular_multiplier_with_edits W hW hsingular
    (fun V : endpoints => V.val) (fun V => V.property)
  refine ⟨m, hlo, hhi, hweight, ?_⟩
  intro V hV
  exact hedit ⟨V, hV⟩

theorem singular_stationary_index_of_multiplier [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0) (m : ℝ)
    (hweight : ∀ f : Variation.WeightDirections μ,
      Variation.weightSecondVariation (chargeOperator W) f f -
        m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) :
    ∃ ν : ℝ, (∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1 := by
  let one := Lp.const 2 μ (1 : ℝ)
  have hyzero := singular_charge_firstVariation_zero W hW hsingular
  obtain ⟨a, ha⟩ := (Variation.weightFirstVariation_eq_zero_iff (adjacencyOperator W)
    (KernelOperator.operator_range_bounded _ _ _ _ one)).mp hsingular
  obtain ⟨y, hy⟩ := (Variation.weightFirstVariation_eq_zero_iff (chargeOperator W)
    (KernelOperator.operator_range_bounded _ _ _ _ one)).mp hyzero
  have hrow : ∀ᵐ x ∂μ, (∫ y', shiftedKernel W m x y' ∂μ) = y - m * a := by
    apply KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    change shiftedOperator W m one = _
    rw [shiftedOperator_eq]
    change chargeOperator W one - m • adjacencyOperator W one = _
    rw [ha, hy, smul_smul, sub_smul]
  let C := (innerSL ℝ one).toLinearMap
  have htest (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ) (hc : C f = 0) :
      ⟪shiftedOperator W m f, f⟫ ≤ 0 := by
    have hmean : (∫ x, f x ∂μ) = 0 := by
      rw [← KernelOperator.inner_constant_one]
      exact hc
    obtain ⟨g, hg⟩ := Variation.exists_direction_of_bounded_mean_zero f hf hmean
    have h := hweight g
    change ⟪chargeOperator W (Variation.directionToL2 g), Variation.directionToL2 g⟫ -
      m * ⟪adjacencyOperator W (Variation.directionToL2 g), Variation.directionToL2 g⟫ ≤ 0 at h
    rw [hg] at h
    rw [shiftedOperator_eq, sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
    exact h
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hindex := KernelOperator.positive_subspace_dimension_le_range_constraints
    (shiftedOperator W m) (KernelOperator.operator_isCompact _ _ _ _)
    (KernelOperator.operator_symmetric _ _ _ _ hsym) C (KernelOperator.boundedL2Submodule μ)
    (KernelOperator.operator_range_bounded _ _ _ _) htest
  exact ⟨y - m * a, hrow, hindex.1, by simpa using hindex.2⟩

/-- The singular capped branch has the same actual kernel signs as the
regular branch, with the stronger positive-index bound one. -/
theorem exists_singular_kernel [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hsingular : Variation.weightFirstVariation (adjacencyOperator W) = 0)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ m ν : ℝ, m ∈ Set.Icc (-3) 1 ∧ HasEditSigns W m ∧
      (∀ f : Variation.WeightDirections μ,
        Variation.weightSecondVariation (chargeOperator W) f f -
          m * Variation.weightSecondVariation (adjacencyOperator W) f f ≤ 0) ∧
      (∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4) ∧
      (∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0) ∧
      (∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν) ∧
      ν = 2 * (objective W - m * density W) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1 := by
  obtain ⟨m, _, _, hweight, hsigns⟩ := exists_singular_common_multiplier W hW hsingular
  obtain ⟨ν, hrow, hfinite, hindex⟩ := singular_stationary_index_of_multiplier W hW hsingular m hweight
  have hbounds := multiplier_bounds_of_editSigns W m hsigns hd0 hdhalf
  refine ⟨m, ν, hbounds, hsigns, hweight, ?_,
    shiftedMoment_complementary_of_editSigns W m hsigns, hrow,
    shifted_stationary_value W m ν hrow, hfinite, hindex⟩
  filter_upwards [shiftedMoment_nonnegative_of_editSigns W m hsigns] with p hp
  refine ⟨hp, ?_⟩
  rw [shiftedMoment_eq]
  have ha := adjacency_moment_mem W p
  have hy := charge_moment_le_adjacency W p
  have hprod := mul_nonneg (by linarith [hbounds.1] : 0 ≤ m + 3) ha.1
  nlinarith [ha.2]

end Erdos1017.CappedModel
