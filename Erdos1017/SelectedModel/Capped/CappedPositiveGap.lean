module

public import Erdos1017.SelectedModel.KernelPositiveGap
public import Erdos1017.SelectedModel.Capped.CappedSecondPositiveDirection

/-!
# Mean-zero eigenvectors with a quantitative gap

A quantitative positive plane for the stationary shifted operator gives a
mean-zero positive eigenvector whose eigenvalue has the same gap, and under norm
convergence with positive index at most two and an index-two limit such
eigenvectors exist eventually.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- An actual quantitative positive plane for the stationary shifted
operator gives an actual meanzero positive eigenvector whose eigenvalue
has the same gap. Its positive index is at most two. -/
theorem exists_meanzero_eigenvector_with_gap_of_coercive_plane
    (V : Model Ω μ) (m ν : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel V m x y ∂μ) = ν)
    [FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m))]
    (hindex : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) ≤ 2)
    (P : Submodule ℝ (Lp ℝ 2 μ)) [FiniteDimensional ℝ P] (hdim : Module.finrank ℝ P = 2)
    (η : ℝ) (hη : 0 < η)
    (hcoercive : ∀ x ∈ P, η * ‖x‖ ^ 2 ≤ ⟪shiftedOperator V m x, x⟫) :
    ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧ 0 < σ ∧
      η ≤ σ ∧ shiftedOperator V m w = σ • w := by
  have hcompact : IsCompactOperator (shiftedOperator V m) := KernelOperator.operator_isCompact _ _ _ _
  have hsym : (shiftedOperator V m).toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric _ _ _ _
    filter_upwards [shiftedMoment_symm V m] with p hp
    exact hp.symm
  have hpositive : ∀ x ∈ P, x ≠ 0 → 0 < ⟪shiftedOperator V m x, x⟫ := by
    intro x hx hx0
    exact (mul_pos hη (sq_pos_of_pos (norm_pos_iff.mpr hx0))).trans_le (hcoercive x hx)
  have htwo : 2 ≤ Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m)) := by
    have h := KernelOperator.positive_subspace_finrank_le_index (shiftedOperator V m) hcompact hsym P hpositive
    rwa [hdim] at h
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := exists_positive_meanzero_eigenvector V m ν hrow htwo
  exact ⟨w, σ, hw, hmean, hσ,
    KernelOperator.positive_eigenvalue_ge_of_coercive_plane (shiftedOperator V m) hcompact hsym hindex
      P hdim η hη hcoercive σ hσ w hw heigen, heigen⟩

/-- Norm convergence of actual stationary shifted operators, finite
positive index at most two and a genuine index-two limit branch give
actual eventual meanzero eigenvectors with a common positive gap.
Compactness, symmetry and the persisting plane are all derived. -/
theorem exists_eventual_meanzero_eigenvalue_gap_of_tendsto
    (V : ℕ → Model Ω μ) (m ν : ℕ → ℝ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hlim : Filter.Tendsto (fun n => shiftedOperator (V n) (m n)) Filter.atTop (nhds T))
    (hrow : ∀ n, ∀ᵐ x ∂μ, (∫ y, shiftedKernel (V n) (m n) x y ∂μ) = ν n)
    (hfinite : ∀ n, FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (V n) (m n))))
    (hindex : ∀ n, Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (V n) (m n))) ≤ 2)
    (hlimit : ¬(FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace T) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace T) ≤ 1)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in Filter.atTop,
      ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧ 0 < σ ∧
        η ≤ σ ∧ shiftedOperator (V n) (m n) w = σ • w := by
  have hcompact (n : ℕ) : IsCompactOperator (shiftedOperator (V n) (m n)) :=
    KernelOperator.operator_isCompact _ _ _ _
  have hsym (n : ℕ) : (shiftedOperator (V n) (m n)).toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric _ _ _ _
    filter_upwards [shiftedMoment_symm (V n) (m n)] with p hp
    exact hp.symm
  have hcompactT := isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall hcompact)
  have hsymT := KernelOperator.symmetric_of_tendsto hlim hsym
  obtain ⟨P, hfiniteP, hdim, η, hη, hpersist⟩ :=
    KernelOperator.two_dimensional_positive_subspace_persists hlim hcompactT hsymT hlimit
  let := hfiniteP
  refine ⟨η, hη, hpersist.mono ?_⟩
  intro n hn
  let := hfinite n
  exact exists_meanzero_eigenvector_with_gap_of_coercive_plane (V n) (m n) (ν n) (hrow n)
    (hindex n) P hdim η hη hn

end Erdos1017.CappedModel
