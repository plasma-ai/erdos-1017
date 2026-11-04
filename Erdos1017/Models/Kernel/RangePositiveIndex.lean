module

public import Erdos1017.Models.Kernel.PositiveIndexBound

/-!
# Positive index from range constraints

If the operator takes values in a test subspace, every nonzero eigenvector lies
in that subspace, so bounded-only tangent tests suffice to control the positive
index (`positive_subspace_dimension_le_range_constraints`).
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- If the operator takes values in a test subspace, every nonzero
eigenvector belongs to that subspace. Thus bounded-only tangent tests can
control positive index without a completion or density assumption. -/
theorem positive_subspace_dimension_le_range_constraints
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T)
    (hsym : T.toLinearMap.IsSymmetric) (C : E →ₗ[ℝ] F)
    (D : Submodule ℝ E) (hrange : ∀ x, T x ∈ D)
    (hquadratic : ∀ x ∈ D, C x = 0 → ⟪T x, x⟫ ≤ 0) :
    FiniteDimensional ℝ (positiveSpectralSubspace T) ∧
      Module.finrank ℝ (positiveSpectralSubspace T) ≤ Module.finrank ℝ F := by
  classical
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T hcompact hsym
  have hmem (i : ι) (hi : 0 < t i) : b i ∈ D := by
    have h := D.smul_mem ((t i)⁻¹) (hrange (b i))
    rwa [heigen i, inv_smul_smul₀ hi.ne'] at h
  obtain ⟨s, hs, hcard⟩ := finite_positive_indices_of_constraints_on_submodule
    T C D hquadratic b t heigen hmem
  have hout (i : ι) (hi : i ∉ s) : t i ≤ 0 := le_of_not_gt (fun hp => hi ((hs i).mpr hp))
  have hsub : positiveSpectralSubspace T ≤ Submodule.span ℝ (↑(s.image b) : Set E) := by
    simpa only [Finset.coe_image] using positiveSpectralSubspace_le_finite_span T hsym b t heigen s hout
  have hfinite := Submodule.finiteDimensional_of_le hsub
  refine ⟨hfinite, ?_⟩
  exact (Submodule.finrank_mono hsub).trans
    ((finrank_span_finset_le_card (R := ℝ) (s.image b)).trans ((Finset.card_image_le).trans hcard))

end Erdos1017.KernelOperator
