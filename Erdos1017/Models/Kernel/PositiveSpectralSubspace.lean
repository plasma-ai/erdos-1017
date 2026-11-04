module

public import Erdos1017.Models.Kernel.SpectralFeatureExistence

/-!
# Span of the positive eigenspaces

`positiveSpectralSubspace` is the algebraic span of all positive eigenspaces of
an operator. When it is finite-dimensional, every orthonormal eigenbasis has
only finitely many positive eigenvalues, and a nonnegative bounded symmetric
measurable kernel then admits a bounded signed Hilbert feature representation
(`exists_bounded_feature_of_finite_positive_subspace`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- The algebraic span of all positive eigenspaces of an operator. -/
def positiveSpectralSubspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) : Submodule ℝ E :=
  ⨆ t : ℝ, ⨆ (_ : 0 < t), Module.End.eigenspace T.toLinearMap t

/-- Finite-dimensionality of the positive spectral subspace forces every
orthonormal eigenbasis to have only finitely many positive eigenvalues. -/
theorem finite_positive_basis_indices {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E)
    [FiniteDimensional ℝ (positiveSpectralSubspace T)]
    (b : HilbertBasis ι ℝ E) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) :
    {i | 0 < t i}.Finite := by
  have hmem (i : {i // 0 < t i}) : b i ∈ positiveSpectralSubspace T := by
    have hle : Module.End.eigenspace T.toLinearMap (t i) ≤ positiveSpectralSubspace T :=
      le_iSup_of_le (t i) (le_iSup_of_le i.property le_rfl)
    exact hle (show b i ∈ Module.End.eigenspace T.toLinearMap (t i) from Module.End.mem_eigenspace_iff.mpr (heigen i))
  let v : {i // 0 < t i} → positiveSpectralSubspace T := fun i => ⟨b i, hmem i⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (positiveSpectralSubspace T).subtype
    exact b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hf : Finite {i // 0 < t i} := hv.finite
  exact Set.finite_coe_iff.mp hf

universe u

/-- Finite positive spectral dimension suffices for a bounded signed Hilbert
feature representation of a nonnegative bounded symmetric measurable kernel.
The eigenbasis and the feature map are constructed, not assumed. -/
theorem exists_bounded_feature_of_finite_positive_subspace
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (hfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB))) :
    ∃ (ι : Type u) (_ : Countable ι) (R : ℝ) (F : Ω → lp (fun _ : ι => ℝ) 2)
      (J : lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 2),
      0 ≤ R ∧ AEStronglyMeasurable F μ ∧ (∀ᵐ x ∂μ, ‖F x‖ ≤ R) ∧
      (∀ f g, ⟪J f, g⟫ = ⟪f, J g⟫) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ⟪J (F z.1), F z.2⟫ := by
  classical
  let := hfinite
  obtain ⟨ι, hcount, b, t, heigen⟩ := exists_countable_eigen_hilbertBasis
    (operator K hB0 hK hB) (operator_isCompact K hB0 hK hB)
    (operator_symmetric K hB0 hK hB hsym)
  let := hcount
  have hs := finite_positive_basis_indices (operator K hB0 hK hB) b t heigen
  let s := hs.toFinset
  have hinside (i : ι) (hi : i ∈ s) : 0 < t i := hs.mem_toFinset.mp hi
  have houtside (i : ι) (hi : i ∉ s) : t i ≤ 0 :=
    le_of_not_gt (fun hp => hi (hs.mem_toFinset.mpr hp))
  obtain ⟨F, hF, hR, _, hrep⟩ := exists_bounded_spectral_feature
    K hB0 hK hB hK0 hsym b t heigen s hinside houtside
  exact ⟨ι, hcount, Real.sqrt (2 * positiveEnergyBound B t s), F, spectralSign t,
    Real.sqrt_nonneg _, hF, hR, spectralSign_self_adjoint t, hrep⟩

end Erdos1017.KernelOperator
