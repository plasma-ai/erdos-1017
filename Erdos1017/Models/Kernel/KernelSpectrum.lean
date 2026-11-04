module

public import Erdos1017.Models.Kernel.KernelCompactness
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral facts for the integral operator

The integral operator is spectrally complete, its nonzero eigenvalues have
finite-dimensional eigenspaces (symmetry not needed), every nonzero
eigenfunction has an essentially bounded representative, and finite collections
of normalized positive eigenfunctions have an explicit diagonal energy bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Spectral completeness for the actual integral operator. -/
theorem eigenspaces_orthogonal_eq_bot (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = K z.2 z.1) :
    (⨆ t : ℝ, Module.End.eigenspace (operator K hB0 hK hB).toLinearMap t)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (operator_isCompact K hB0 hK hB) (operator_symmetric K hB0 hK hB hsym)

/-- Nonzero eigenvalues of the integral operator have finite-dimensional
eigenspaces. Symmetry is unnecessary for this conclusion. -/
theorem finiteDimensional_eigenspace (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (t : ℝ) (ht : t ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (operator K hB0 hK hB).toLinearMap t) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (operator_isCompact K hB0 hK hB) t ht

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- Every nonzero eigenfunction has an essentially bounded representative,
with the bound obtained from its actual integral equation. -/
theorem eigenfunction_bound (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : t ≠ 0)
    (heigen : operator K hB0 hK hB f = t • f) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ B * ‖f‖ / ‖t‖ := by
  have hcoe : ⇑(onL2 K hK hB f) =ᵐ[μ] t • ⇑f := by
    change ⇑(operator K hB0 hK hB f) =ᵐ[μ] t • ⇑f
    rw [heigen]
    exact Lp.coeFn_smul t f
  filter_upwards [hcoe, onL2_coe K hK hB f,
    applyKernel_bound hB ((Lp.memLp f).integrable (by norm_num))] with x heq hx hb
  rw [← hx, heq, Pi.smul_apply, norm_smul] at hb
  apply (le_div_iff₀ (norm_pos_iff.mpr ht)).mpr
  rw [mul_comm]
  exact hb.trans (mul_le_mul_of_nonneg_left (integral_norm_le_L2 f) hB0)

omit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The diagonal energy of any finite collection of normalized positive
eigenfunctions has an explicit essential bound. -/
theorem finite_positive_energy_bound {ι : Type*} [Fintype ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (f : ι → Lp ℝ 2 μ) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (hnorm : ∀ i, ‖f i‖ = 1)
    (heigen : ∀ i, operator K hB0 hK hB (f i) = t i • f i) :
    ∀ᵐ x ∂μ, ∑ i, t i * (f i x) ^ 2 ≤ B ^ 2 * ∑ i, (t i)⁻¹ := by
  have hall : ∀ᵐ x ∂μ, ∀ i, ‖f i x‖ ≤ B / t i := by
    apply ae_all_iff.mpr
    intro i
    simpa [hnorm i, Real.norm_of_nonneg (ht i).le] using
      eigenfunction_bound K hB0 hK hB (f i) (t i) (ht i).ne' (heigen i)
  filter_upwards [hall] with x hx
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs : (f i x) ^ 2 ≤ (B / t i) ^ 2 := by
    have hb := hx i
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    t i * (f i x) ^ 2 ≤ t i * (B / t i) ^ 2 := mul_le_mul_of_nonneg_left hs (ht i).le
    _ = B ^ 2 * (t i)⁻¹ := by field_simp

end Erdos1017.KernelOperator
