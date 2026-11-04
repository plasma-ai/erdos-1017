module

public import Erdos1017.SelectedModel.Structure.CanonicalFeatureRows
public import Erdos1017.SelectedModel.Structure.FullIndexTwoKernelGeometry

/-!
# Canonical row factorization of a full optimizer

One full stationary optimizer has a canonical feature and a strongly measurable
row map whose equalities agree at every pair of points in one common measurable
conull set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- One actual full stationary optimizer has a canonical feature and an
actual strongly measurable row map whose equalities agree at every pair
of points in one common measurable conull set. -/
theorem FullStationaryClass.exists_canonical_row_factorization
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∃ (σ : ℝ), 0 < σ ∧ ∃ (ι : Type u) (_ : Countable ι)
      (φ : Ω → ℝ) (V : Ω → lp (fun _ : ι => ℝ) 2)
      (R : Ω → Lp ℝ 2 μ) (S : Set Ω),
      KernelOperator.CanonicalIndexTwoFeature μ (shiftedKernel W m) 4
        (2 * (c - m * d)) σ φ V ∧
      StronglyMeasurable R ∧ (∀ x, ‖R x‖ ≤ 4) ∧
      MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ S) ∧
      (∀ x ∈ S, (R x : Ω → ℝ) =ᵐ[μ] shiftedKernel W m x) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        (shiftedKernel W m x =ᵐ[μ] shiftedKernel W m y) ↔ φ x = φ y ∧ V x = V y) ∧
      (∀ x ∈ S, ∀ y ∈ S, R x = R y ↔ φ x = φ y ∧ V x = V y) := by
  obtain ⟨σ, hσ, ι, hcount, φ, V, hcanonical⟩ :=
    hW.exists_canonical_index_two_feature hd hgap
  let := hcount
  have hbound : ∀ᵐ p ∂μ.prod μ, ‖shiftedKernel W m p.1 p.2‖ ≤ 4 := by
    filter_upwards [hW.moment_mem] with p hp
    change ‖shiftedMoment W m p‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  obtain ⟨R, hR, hrow, hnorm⟩ := KernelOperator.exists_stronglyMeasurable_rowMap
    (shiftedKernel W m) 4 (by norm_num) (shiftedKernel_measurable W m) hbound
  obtain ⟨S, hS, hSae, hrowS, hrows, hmap⟩ :=
    hcanonical.exists_conull_rowMap_feature_iff hσ R hrow
  exact ⟨σ, hσ, ι, hcount, φ, V, R, S, hcanonical, hR, hnorm, hS, hSae,
    hrowS, hrows, hmap⟩

end Erdos1017.CappedModel
