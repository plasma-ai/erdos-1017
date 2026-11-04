module

public import Erdos1017.Models.Kernel.PositiveIndexBound

/-!
# Positive index bounds from bounded tangent tests

Only bounded variation directions are needed for the positive-index bound, since
every positive kernel eigenfunction is essentially bounded; two scalar tangent
constraints on bounded L² directions give positive spectral index at most two,
and one constraint gives at most one.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

/-- The linear subspace of L² classes admitting an essential uniform bound. -/
def boundedL2Submodule {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ C}
  zero_mem' := by
    change ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂μ, ‖(0 : Lp ℝ 2 μ) x‖ ≤ C
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    change (0 : Lp ℝ 2 μ) x = 0 at hx
    rw [hx]
    norm_num
  add_mem' := by
    rintro f g ⟨B, hB, hb⟩ ⟨C, hC, hc⟩
    refine ⟨B + C, add_nonneg hB hC, ?_⟩
    filter_upwards [hb, hc, Lp.coeFn_add f g] with x hx hy heq
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hx hy)
  smul_mem' := by
    rintro c f ⟨B, hB, hb⟩
    refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg _) hB, ?_⟩
    filter_upwards [hb, Lp.coeFn_smul c f] with x hx heq
    rw [heq]
    change ‖c • f x‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- Only bounded variation directions are needed for the positive-index
bound: every positive kernel eigenfunction is essentially bounded, as are
its finite linear combinations. -/
theorem positive_subspace_dimension_le_bounded_constraints
    {Ω F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (C : Lp ℝ 2 μ →ₗ[ℝ] F)
    (hquadratic : ∀ f ∈ boundedL2Submodule μ, C f = 0 →
      ⟪operator K hB0 hK hB f, f⟫ ≤ 0) :
    FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ∧
      Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ≤
        Module.finrank ℝ F := by
  classical
  let T := operator K hB0 hK hB
  have hsymmetric := operator_symmetric K hB0 hK hB hsym
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T (operator_isCompact K hB0 hK hB) hsymmetric
  have hmem (i : ι) (hi : 0 < t i) : b i ∈ boundedL2Submodule μ := by
    refine ⟨B * ‖b i‖ / |t i|, by positivity, ?_⟩
    exact eigenfunction_bound K hB0 hK hB (b i) (t i) hi.ne' (heigen i)
  obtain ⟨s, hs, hcard⟩ := finite_positive_indices_of_constraints_on_submodule
    T C (boundedL2Submodule μ) hquadratic b t heigen hmem
  have hout (i : ι) (hi : i ∉ s) : t i ≤ 0 := le_of_not_gt (fun hp => hi ((hs i).mpr hp))
  have hsub : positiveSpectralSubspace T ≤ Submodule.span ℝ (↑(s.image b) : Set (Lp ℝ 2 μ)) := by
    simpa only [Finset.coe_image] using
      positiveSpectralSubspace_le_finite_span T hsymmetric b t heigen s hout
  have hfinite := Submodule.finiteDimensional_of_le hsub
  refine ⟨hfinite, ?_⟩
  exact (Submodule.finrank_mono hsub).trans
    ((finrank_span_finset_le_card (R := ℝ) (s.image b)).trans ((Finset.card_image_le).trans hcard))

/-- The two scalar tangent constraints in the nonconstant-degree case give
positive spectral index at most two. Both constraints are imposed only on
bounded L² directions. -/
theorem positive_index_le_two_of_bounded_tangent_tests
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (u v : Lp ℝ 2 μ)
    (hquadratic : ∀ f ∈ boundedL2Submodule μ, ⟪u, f⟫ = 0 → ⟪v, f⟫ = 0 →
      ⟪operator K hB0 hK hB f, f⟫ ≤ 0) :
    FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ∧
      Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ≤ 2 := by
  let C := (innerSL ℝ u).toLinearMap.prod (innerSL ℝ v).toLinearMap
  have hq (f : Lp ℝ 2 μ) (hf : f ∈ boundedL2Submodule μ) (hc : C f = 0) :
      ⟪operator K hB0 hK hB f, f⟫ ≤ 0 := by
    exact hquadratic f hf (congrArg Prod.fst hc) (congrArg Prod.snd hc)
  simpa using positive_subspace_dimension_le_bounded_constraints K hB0 hK hB hsym C hq

/-- One scalar tangent constraint gives positive spectral index at most one. -/
theorem positive_index_le_one_of_bounded_tangent_tests
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (u : Lp ℝ 2 μ)
    (hquadratic : ∀ f ∈ boundedL2Submodule μ, ⟪u, f⟫ = 0 →
      ⟪operator K hB0 hK hB f, f⟫ ≤ 0) :
    FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ∧
      Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ≤ 1 := by
  simpa using positive_subspace_dimension_le_bounded_constraints
    K hB0 hK hB hsym (innerSL ℝ u).toLinearMap hquadratic

end Erdos1017.KernelOperator
