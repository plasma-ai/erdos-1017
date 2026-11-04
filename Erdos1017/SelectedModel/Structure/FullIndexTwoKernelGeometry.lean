module

public import Erdos1017.SelectedModel.Structure.IndexTwoKernelGeometry
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.Models.Capped.CappedSelectedTrace

/-!
# Canonical index-two representation of a full optimizer

The full stationary optimizer and its recorded multiplier have a canonical
index-two representation with its eigenvalue, normalized scalar coordinate and
negative feature (`exists_canonical_index_two_feature`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The same full stationary optimizer and recorded multiplier have a
canonical index-two representation. The eigenvalue, normalized scalar
coordinate and countable negative feature are all constructed. -/
theorem FullStationaryClass.exists_canonical_index_two_feature
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ (σ : ℝ), 0 < σ ∧ ∃ (ι : Type u) (_ : Countable ι)
      (φ : Ω → ℝ) (V : Ω → lp (fun _ : ι => ℝ) 2),
      KernelOperator.CanonicalIndexTwoFeature μ (shiftedKernel W m) 4
        (2 * (c - m * d)) σ φ V := by
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨w, σ, hw, hmean, hσ, heigen⟩ := hs.positive_eigenvector
  have hbound : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hfour := shiftedOperator_eq_of_bound W m (by norm_num : (0 : ℝ) ≤ 4) hbound
  have hfinite : FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (KernelOperator.operator (shiftedKernel W m)
        (by norm_num) (shiftedKernel_measurable W m) hbound)) := by
    rw [← hfour]
    exact hW.finite_positive
  have hindex : Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (KernelOperator.operator (shiftedKernel W m)
        (by norm_num) (shiftedKernel_measurable W m) hbound)) ≤ 2 := by
    rw [← hfour]
    exact hW.index_le_two
  have heigenFour : KernelOperator.operator (shiftedKernel W m)
      (by norm_num) (shiftedKernel_measurable W m) hbound w = σ • w := by
    rw [← hfour]
    exact heigen
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  obtain ⟨ι, hcount, φ, V, hcanonical⟩ := KernelOperator.exists_index_two_feature
    (shiftedKernel W m) (by norm_num) (shiftedKernel_measurable W m) hbound
    (hW.moment_mem.mono (fun _ hp => hp.1)) hsym (2 * (c - m * d))
    hs.stationary_pos hW.stationary hfinite hindex w hw hmean σ hσ heigenFour
  exact ⟨σ, hσ, ι, hcount, φ, V, hcanonical⟩

end Erdos1017.CappedModel
