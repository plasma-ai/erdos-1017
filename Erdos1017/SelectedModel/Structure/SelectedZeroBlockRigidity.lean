module

public import Erdos1017.SelectedModel.Structure.AffineKernelRowEnergy
public import Erdos1017.SelectedModel.Selection.QuadraticMomentResidual
public import Erdos1017.SelectedModel.Structure.ZeroBlockAffineRows
public import Erdos1017.SelectedModel.Structure.FullIndexTwoKernelGeometry

/-!
# Two row values on zero blocks

Maximum-energy selection permits at most two whole shifted row values on a
measurable affine row block, so every positive-measure zero block of the
selected strict-gap kernel has at most two whole row values, via canonical
features, affine rows and the supported residual.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual maximum-energy selection permits at most two whole shifted row
values on a measurable affine row block. A nonconstant row slope uses the
constructed supported residual; a zero slope already has one row value. -/
theorem FullStationaryClass.affine_rows_two_values_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (E : Set Ω) (hE : MeasurableSet E) (P R : Lp ℝ 2 μ) (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B)
    (hrows : ∀ᵐ x ∂μ, x ∈ E → ∀ᵐ y ∂μ,
      shiftedKernel W m x y = P y + φ x * R y) :
    ∃ Q₁ Q₂ : Lp ℝ 2 μ, ∀ᵐ x ∂μ, x ∈ E →
      (∀ᵐ y ∂μ, shiftedKernel W m x y = Q₁ y) ∨
      (∀ᵐ y ∂μ, shiftedKernel W m x y = Q₂ y) := by
  rcases eq_or_ne R 0 with rfl | hR
  · refine ⟨P, P, ?_⟩
    filter_upwards [hrows] with x hx hxe
    left
    filter_upwards [hx hxe, Lp.coeFn_zero ℝ 2 μ] with y hy hz
    change (0 : Lp ℝ 2 μ) y = 0 at hz
    simpa only [hz, mul_zero, add_zero] using hy
  · have hvalues : ∃ a b : ℝ, ∀ᵐ x ∂μ.restrict E, φ x = a ∨ φ x = b := by
      by_contra hnot
      obtain ⟨f, hf, hsupport, hmean, hmoment, hpositive⟩ :=
        KernelOperator.exists_supported_positive_quadratic_moment_residual
          E hE φ hφ hB0 hB hnot
      have hzero := hW.affine_rows_quadratic_moment_eq_zero_of_strict_gap
        hd hgap hmax E P R hR φ hφ hB hrows f hf hsupport hmean hmoment
      rw [hzero] at hpositive
      exact (lt_irrefl 0) hpositive
    obtain ⟨a, b, hvalues⟩ := hvalues
    refine ⟨P + a • R, P + b • R, ?_⟩
    filter_upwards [hrows, (ae_restrict_iff' hE).mp hvalues] with x hx hvalue hxe
    rcases hvalue hxe with hxa | hxb
    · left
      filter_upwards [hx hxe, Lp.coeFn_add P (a • R), Lp.coeFn_smul a R]
        with y hy hadd hsmul
      rw [hy, hxa, hadd]
      simp only [Pi.add_apply]
      rw [hsmul]
      rfl
    · right
      filter_upwards [hx hxe, Lp.coeFn_add P (b • R), Lp.coeFn_smul b R]
        with y hy hadd hsmul
      rw [hy, hxb, hadd]
      simp only [Pi.add_apply]
      rw [hsmul]
      rfl

/-- Every positive-measure zero block of the actual selected strict-gap
kernel has at most two whole row values. Canonical features, their affine
rows and the supported residual obstruction are all constructed internally. -/
theorem FullStationaryClass.zero_block_two_rows_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (E : Set Ω) (hE : MeasurableSet E) (hEpos : μ E ≠ 0)
    (hzero : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E),
      shiftedKernel W m p.1 p.2 = 0) :
    ∃ Q₁ Q₂ : Lp ℝ 2 μ, ∀ᵐ x ∂μ, x ∈ E →
      (∀ᵐ y ∂μ, shiftedKernel W m x y = Q₁ y) ∨
      (∀ᵐ y ∂μ, shiftedKernel W m x y = Q₂ y) := by
  obtain ⟨σ, hσ, ι, hcount, φ, V, hfeature⟩ := hW.exists_canonical_index_two_feature hd hgap
  have : Countable ι := hcount
  have hφB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ 4 / σ :=
    Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hfeature.scalar_bound x
  obtain ⟨P, R, _, _, hrows⟩ := KernelOperator.exists_affine_rows_of_zero_block
    (shiftedKernel W m) E hE hEpos V hfeature.feature_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hfeature.feature_bound) φ
    hfeature.scalar_measurable.aestronglyMeasurable hφB
    (2 * (c - m * d)) σ hfeature.representation hzero
  exact hW.affine_rows_two_values_of_strict_gap hd hgap hmax E hE P R φ
    hfeature.scalar_measurable.aestronglyMeasurable (by positivity) hφB hrows

end Erdos1017.CappedModel
