module

public import Erdos1017.Models.Kernel.SetIntegralNormBound
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Pointwise energy bounds from cell averages

Bounds on all cell averages control the pointwise squared energy of a finite
family, also in a weighted form; this is the finite-dimensional step of the
spectral feature construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

/-- Bounds on all cell averages control the pointwise squared energy of a
finite family. This is the finite-dimensional step of the spectral feature
construction. -/
theorem ae_sum_sq_le_of_setIntegral_sum_sq_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Fintype ι] (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, MeasurableSet s →
      (∑ i, (∫ x in s, f i x ∂μ) ^ 2) ≤ C ^ 2 * (μ.real s) ^ 2) :
    ∀ᵐ x ∂μ, ∑ i, (f i x) ^ 2 ≤ C ^ 2 := by
  let e := EuclideanSpace.basisFun ι ℝ
  let F : Ω → EuclideanSpace ℝ ι := fun x => ∑ i, f i x • e i
  have hF : Integrable F μ := integrable_finsetSum _ (fun i _ => (hf i).smul_const (e i))
  have hnorm (a : ι → ℝ) : ‖∑ i, a i • e i‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, e.orthonormal.inner_sum]
    simp [pow_two]
  have hset (s : Set Ω) (hs : MeasurableSet s) : ‖∫ x in s, F x ∂μ‖ ≤ C * μ.real s := by
    have hi : (∫ x in s, F x ∂μ) = ∑ i, (∫ x in s, f i x ∂μ) • e i := by
      rw [show F = (fun x => ∑ i, f i x • e i) from rfl,
        integral_finsetSum _ (fun i _ => ((hf i).smul_const (e i)).integrableOn)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_smul_const _ _
    rw [hi]
    have hsq := hbound s hs
    rw [← hnorm] at hsq
    nlinarith [norm_nonneg (∑ i, (∫ x in s, f i x ∂μ) • e i),
      mul_nonneg hC (measureReal_nonneg (μ := μ) (s := s))]
  filter_upwards [ae_norm_le_of_setIntegral_norm_le hF C hC hset] with x hx
  rw [show F x = ∑ i, f i x • e i from rfl] at hx
  rw [← hnorm]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

/-- Weighted cell-energy control gives weighted pointwise energy control. -/
theorem ae_weighted_sum_sq_le_of_setIntegral_sum_sq_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Fintype ι] (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ s, MeasurableSet s →
      (∑ i, w i * (∫ x in s, f i x ∂μ) ^ 2) ≤ D * (μ.real s) ^ 2) :
    ∀ᵐ x ∂μ, ∑ i, w i * (f i x) ^ 2 ≤ D := by
  let g : ι → Ω → ℝ := fun i x => Real.sqrt (w i) * f i x
  have hconv (a : ι → ℝ) : (∑ i, (Real.sqrt (w i) * a i) ^ 2) =
      ∑ i, w i * (a i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hg (i : ι) : Integrable (g i) μ := (hf i).const_mul _
  have h := ae_sum_sq_le_of_setIntegral_sum_sq_le g hg (Real.sqrt D) (Real.sqrt_nonneg D) (by
    intro s hs
    simp only [g, integral_const_mul]
    rw [hconv, Real.sq_sqrt hD]
    exact hbound s hs)
  simpa only [g, hconv, Real.sq_sqrt hD] using h

end Erdos1017.KernelOperator
