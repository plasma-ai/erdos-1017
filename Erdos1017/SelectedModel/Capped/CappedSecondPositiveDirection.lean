module

public import Erdos1017.SelectedModel.Selection.FullPositiveEigenvector
public import Erdos1017.SelectedModel.AnchoredEigenbasis

/-!
# Second positive direction from positive index two

A compact symmetric operator with positive spectral dimension at least two has a
positive eigenvector orthogonal to any given unit eigenvector, which supplies a
positive mean-zero eigenvector of the stationary shifted kernel and hence
positive gamma and strict support.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- A compact symmetric operator with positive spectral dimension at least
two has a positive eigenvector orthogonal to any specified unit
eigenvector. The specified eigenvalue may have either sign or be zero. -/
theorem exists_positive_eigenvector_orthogonal_to_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hcompact : IsCompactOperator T) (hsym : T.toLinearMap.IsSymmetric)
    (v : E) (hv : ‖v‖ = 1) (ν : ℝ) (heigen : T v = ν • v)
    [FiniteDimensional ℝ (positiveSpectralSubspace T)]
    (hindex : 2 ≤ Module.finrank ℝ (positiveSpectralSubspace T)) :
    ∃ (w : E) (σ : ℝ), w ≠ 0 ∧ ⟪v, w⟫ = 0 ∧ 0 < σ ∧ T w = σ • w := by
  classical
  obtain ⟨ι, b, t, i₀, ht, hb₀, _⟩ := exists_eigen_hilbertBasis_containing
    T hcompact hsym v hv ν heigen
  have hex : ∃ i, i ≠ i₀ ∧ 0 < t i := by
    by_contra h
    push Not at h
    have hout (i : ι) (hi : i ∉ ({i₀} : Finset ι)) : t i ≤ 0 := by
      exact h i (by simpa using hi)
    have hsub : positiveSpectralSubspace T ≤
        Submodule.span ℝ (↑(({i₀} : Finset ι).image b) : Set E) := by
      simpa only [Finset.coe_image] using
        positiveSpectralSubspace_le_finite_span T hsym b t ht {i₀} hout
    have hdim := (Submodule.finrank_mono hsub).trans
      ((finrank_span_finset_le_card (R := ℝ) (({i₀} : Finset ι).image b)).trans
        (Finset.card_image_le))
    simp only [Finset.card_singleton] at hdim
    omega
  obtain ⟨i, hi, hpos⟩ := hex
  refine ⟨b i, t i, ?_, ?_, hpos, ht i⟩
  · intro hz
    have hn := b.orthonormal.norm_eq_one i
    rw [hz, norm_zero] at hn
    norm_num at hn
  · rw [← hb₀]
    exact b.orthonormal.inner_eq_zero hi.symm

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Positive spectral dimension at least two supplies an actual positive
meanzero eigenvector of the stationary shifted kernel. No sign assumption
on the stationary value is required. -/
theorem exists_positive_meanzero_eigenvector [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))]
    (hindex : 2 ≤ Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))) :
    ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧ 0 < σ ∧
      shiftedOperator W m w = σ • w := by
  have hsym : (shiftedOperator W m).toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric _ _ _ _
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have heigen : shiftedOperator W m (Lp.const 2 μ (1 : ℝ)) = ν • Lp.const 2 μ (1 : ℝ) :=
    KernelOperator.constant_one_eigenvector_of_stationary _ _ _ _ ν hrow
  obtain ⟨w, σ, hw, horth, hσ, heig⟩ := KernelOperator.exists_positive_eigenvector_orthogonal_to_unit
    (shiftedOperator W m) (KernelOperator.operator_isCompact _ _ _ _) hsym
    (Lp.const 2 μ (1 : ℝ)) KernelOperator.constant_one_norm ν heigen hindex
  exact ⟨w, σ, hw, by rwa [KernelOperator.inner_constant_one] at horth, hσ, heig⟩

theorem full_gamma_pos_of_positive_index_two [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    [StandardBorelSpace Ω] [NullSingletonClass μ]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hdhalf : density W < 1 / 2)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))]
    (hindex : 2 ≤ Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))) :
    0 < ν + m := by
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := exists_positive_meanzero_eigenvector W m ν hrow hindex
  exact full_gamma_pos_of_positive_eigenvector W hW hopt m ν hrow hregular hdhalf w hw hmean σ hσ heigen

theorem full_strict_support_of_positive_index_two [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W)
    (hopt : objective W = FractionalGraph.densityLimit (density W))
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))]
    (hindex : 2 ≤ Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := exists_positive_meanzero_eigenvector W m ν hrow hindex
  exact full_strict_support_of_positive_eigenvector W hW hopt m ν hrow hregular
    w hw hmean σ hσ heigen hnonneg hcomp

theorem strict_support_of_positive_index_two [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (m ν : ℝ) (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ, (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))]
    (hindex : 2 ≤ Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := exists_positive_meanzero_eigenvector W m ν hrow hindex
  exact strict_support_of_positive_eigenvector W hW m ν hrow hregular
    w hw hmean σ hσ heigen hnonneg hcomp

end Erdos1017.CappedModel
