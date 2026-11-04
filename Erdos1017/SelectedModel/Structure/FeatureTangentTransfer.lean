module

public import Erdos1017.SelectedModel.Structure.SupportFeatureBarycenters
public import Erdos1017.SelectedModel.Structure.FeatureBilinearMoments
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Transfer of the tangent inequality to feature support

This module defines the degree-tangent combination of two oriented feature
differences and its bilinear form, and transfers the physical tangent
inequality, evaluated at Bochner barycenters of mean-one densities, to every
quadruple in the support of the joint feature law, giving nonnegative mutual
energy of two oriented zero pairs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Erdos1017.KernelOperator

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The exact degree-tangent combination of two oriented feature differences. -/
def degreeTangentVector (ℓ : E →L[ℝ] ℝ) (a b c d : E) : E :=
  ℓ (c - d) • (a - b) - ℓ (a - b) • (c - d)

/-- The original bilinear form evaluated on the exact tangent vector. -/
def degreeTangentForm (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ)
    (a b c d : E) : ℝ :=
  B (degreeTangentVector ℓ a b c d) (degreeTangentVector ℓ a b c d)

omit [CompleteSpace E] in
/-- The limiting test is continuous in all four joint feature coordinates. -/
theorem continuous_degreeTangentForm (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) :
    Continuous (fun a : Fin 4 → E => degreeTangentForm B ℓ (a 0) (a 1) (a 2) (a 3)) := by
  unfold degreeTangentForm degreeTangentVector
  fun_prop

/-- Four actual mean-one densities produce an exact physical tangent
before any limit. The bilinear test is evaluated at their Bochner
barycenters, by the proved physical kernel moment identity. -/
theorem degreeTangentForm_barycenters_nonpositive
    (K : Ω → Ω → ℝ) (F : Ω → E) (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → kernelEnergy (μ := μ) K f ≤ 0)
    (ρ : Fin 4 → Ω → ℝ) (hρ : ∀ i, Integrable (ρ i) μ)
    (hρF : ∀ i, Integrable (fun x => ρ i x • F x) μ)
    (hmean : ∀ i, (∫ x, ρ i x ∂μ) = 1) :
    degreeTangentForm B ℓ (∫ x, ρ 0 x • F x ∂μ) (∫ x, ρ 1 x • F x ∂μ)
      (∫ x, ρ 2 x • F x ∂μ) (∫ x, ρ 3 x • F x ∂μ) ≤ 0 := by
  let u := fun x => ρ 0 x - ρ 1 x
  let v := fun x => ρ 2 x - ρ 3 x
  let U := ∫ x, u x • F x ∂μ
  let V := ∫ x, v x • F x ∂μ
  let f := fun x => ℓ V * u x - ℓ U * v x
  have hu : Integrable u μ := (hρ 0).sub (hρ 1)
  have hv : Integrable v μ := (hρ 2).sub (hρ 3)
  have hum : (∫ x, u x ∂μ) = 0 := by
    rw [show u = (fun x => ρ 0 x - ρ 1 x) from rfl, integral_sub (hρ 0) (hρ 1),
      hmean 0, hmean 1, sub_self]
  have hvm : (∫ x, v x ∂μ) = 0 := by
    rw [show v = (fun x => ρ 2 x - ρ 3 x) from rfl, integral_sub (hρ 2) (hρ 3),
      hmean 2, hmean 3, sub_self]
  have huF : Integrable (fun x => u x • F x) μ := by
    convert (hρF 0).sub (hρF 1) using 1
    funext x
    simp only [u, sub_smul, Pi.sub_apply]
  have hvF : Integrable (fun x => v x • F x) μ := by
    convert (hρF 2).sub (hρF 3) using 1
    funext x
    simp only [v, sub_smul, Pi.sub_apply]
  have hf : Integrable f μ := (hu.const_mul (ℓ V)).sub (hv.const_mul (ℓ U))
  have hfF : Integrable (fun x => f x • F x) μ := by
    convert (huF.smul (ℓ V)).sub (hvF.smul (ℓ U)) using 1
    funext x
    simp only [f, sub_smul, mul_smul, Pi.sub_apply, Pi.smul_apply]
  have hfm : (∫ x, f x ∂μ) = 0 := by
    rw [show f = (fun x => ℓ V * u x - ℓ U * v x) from rfl,
      integral_sub (hu.const_mul (ℓ V)) (hv.const_mul (ℓ U)),
      integral_const_mul, integral_const_mul, hum, hvm, mul_zero, mul_zero, sub_self]
  have hfb : (∫ x, f x • F x ∂μ) = ℓ V • U - ℓ U • V := by
    change (∫ x, (ℓ V * u x - ℓ U * v x) • F x ∂μ) = _
    simp_rw [sub_smul, mul_smul]
    have heU : Integrable (fun x => ℓ V • (u x • F x)) μ := huF.smul (ℓ V)
    have heV : Integrable (fun x => ℓ U • (v x • F x)) μ := hvF.smul (ℓ U)
    rw [integral_sub heU heV, integral_smul, integral_smul]
  have hfd : (∫ x, ℓ (F x) * f x ∂μ) = 0 := by
    rw [integral_feature_degree F ℓ f hfF, hfb, map_sub, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have hq := hnonpos f hf hfm hfd
  rw [kernelEnergy_eq_bilinear_barycenter K F B hrep f hfF, hfb] at hq
  have hU : U = (∫ x, ρ 0 x • F x ∂μ) - ∫ x, ρ 1 x • F x ∂μ := by
    change (∫ x, (ρ 0 x - ρ 1 x) • F x ∂μ) = _
    simp_rw [sub_smul]
    exact integral_sub (hρF 0) (hρF 1)
  have hV : V = (∫ x, ρ 2 x • F x ∂μ) - ∫ x, ρ 3 x • F x ∂μ := by
    change (∫ x, (ρ 2 x - ρ 3 x) • F x ∂μ) = _
    simp_rw [sub_smul]
    exact integral_sub (hρF 2) (hρF 3)
  rw [hU, hV] at hq
  exact hq

omit [CompleteSpace E] in
/-- On a common strict degree cone, two nonnegative self-forms have
nonnegative mixed pairing whenever their exact tangent combination has
nonpositive energy. No index or positive-semidefinite assumption is used. -/
theorem bilinear_cross_nonnegative_of_tangent
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (ℓ : E →L[ℝ] ℝ) (u v : E) (hu : 0 ≤ B u u) (hv : 0 ≤ B v v)
    (hdu : 0 < ℓ u) (hdv : 0 < ℓ v)
    (htan : B (ℓ v • u - ℓ u • v) (ℓ v • u - ℓ u • v) ≤ 0) :
    0 ≤ B u v := by
  have heq : B (ℓ v • u - ℓ u • v) (ℓ v • u - ℓ u • v) =
      (ℓ v) ^ 2 * B u u + (ℓ u) ^ 2 * B v v - 2 * ℓ u * ℓ v * B u v := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
    rw [hsym v u]
    ring
  rw [heq] at htan
  have hself := add_nonneg (mul_nonneg (sq_nonneg (ℓ v)) hu)
    (mul_nonneg (sq_nonneg (ℓ u)) hv)
  have hscale : 0 < 2 * ℓ u * ℓ v := by positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp (by linarith : 0 ≤ (2 * ℓ u * ℓ v) * B u v)

variable [MeasurableSpace E] [BorelSpace E]

/-- Actual conditional barycenters transfer the original physical tangent
inequality to every quadruple in the support of the actual joint feature law.
No tangent inequality on the support is assumed. -/
theorem degreeTangentForm_nonpositive_on_support
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : StronglyMeasurable F)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → kernelEnergy (μ := μ) K f ≤ 0)
    (a : Fin 4 → E) (ha : ∀ i, a i ∈ (μ.map F).support) :
    degreeTangentForm B ℓ (a 0) (a 1) (a 2) (a 3) ≤ 0 := by
  let ε := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ρ := fun n i => featureBallDensity (μ := μ) F (a i) (ε n)
  let A := fun n i => ∫ x, ρ n i x • F x ∂μ
  have hA : ∀ i, Tendsto (fun n => A n i) atTop (𝓝 (a i)) := fun i =>
    featureBallDensity_barycenter_tendsto F hF (a i) (ha i) ε hε hεlim
  have hlim : Tendsto A atTop (𝓝 a) := tendsto_pi_nhds.mpr hA
  have hq := (continuous_degreeTangentForm B ℓ).continuousAt.tendsto.comp hlim
  apply le_of_tendsto' hq
  intro n
  exact degreeTangentForm_barycenters_nonpositive K F B ℓ hrep hnonpos (ρ n)
    (fun i => featureBallDensity_integrable F hF (a i) (ε n))
    (fun i => featureBallDensity_smul_integrable F hF (a i) (ε n))
    (fun i => featureBallDensity_integral F hF (a i) (ha i) (ε n) (hε n))

/-- Two oriented zero pairs at actual joint feature support points have
nonnegative mutual energy. Diagonal nonnegativity is required only at
the four endpoints; the support tangent inequality is proved above. -/
theorem bilinear_missing_pair_cross_nonnegative_on_support
    (K : Ω → Ω → ℝ) (F : Ω → E) (hF : StronglyMeasurable F)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (ℓ : E →L[ℝ] ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = B (F p.1) (F p.2))
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      (∫ x, ℓ (F x) * f x ∂μ) = 0 → kernelEnergy (μ := μ) K f ≤ 0)
    (a : Fin 4 → E) (ha : ∀ i, a i ∈ (μ.map F).support)
    (hdiag : ∀ i, 0 ≤ B (a i) (a i))
    (hzero₀ : B (a 0) (a 1) = 0) (hzero₁ : B (a 2) (a 3) = 0)
    (hdegree₀ : 0 < ℓ (a 0 - a 1)) (hdegree₁ : 0 < ℓ (a 2 - a 3)) :
    0 ≤ B (a 0 - a 1) (a 2 - a 3) := by
  have hself₀ : 0 ≤ B (a 0 - a 1) (a 0 - a 1) := by
    simp only [map_sub, sub_apply]
    rw [hsym (a 1) (a 0), hzero₀]
    linarith [hdiag 0, hdiag 1]
  have hself₁ : 0 ≤ B (a 2 - a 3) (a 2 - a 3) := by
    simp only [map_sub, sub_apply]
    rw [hsym (a 3) (a 2), hzero₁]
    linarith [hdiag 2, hdiag 3]
  exact bilinear_cross_nonnegative_of_tangent B hsym ℓ _ _ hself₀ hself₁ hdegree₀ hdegree₁
    (degreeTangentForm_nonpositive_on_support K F hF B ℓ hrep hnonpos a ha)

end Erdos1017.KernelOperator
