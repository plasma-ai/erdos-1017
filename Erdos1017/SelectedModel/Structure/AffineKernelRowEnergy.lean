module

public import Erdos1017.Models.Kernel.KernelOperator
public import Erdos1017.SelectedModel.Selection.FullStationaryEnergyVariation

/-!
# Energy of affine kernel rows

A supported direction orthogonal to the two affine row coefficients is a null
vector of the symmetric integral operator, with squared-kernel energy
coefficient equal to the squared row slope times its quadratic moment, so
maximum-energy selection rules out a positive quadratic moment on a nonconstant
affine row block.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem integral_real_sq (P : Lp ℝ 2 μ) :
    (∫ y, (P y) ^ 2 ∂μ) = ‖P‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with y
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem integral_real_mul (P R : Lp ℝ 2 μ) :
    (∫ y, P y * R y ∂μ) = ⟪P, R⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with y
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem affine_row_pairing (K : Ω → Ω → ℝ) (P R g : Lp ℝ 2 μ)
    (φ : Ω → ℝ) (x : Ω)
    (hrow : ∀ᵐ y ∂μ, K x y = P y + φ x * R y) :
    applyKernel (μ := μ) K g x = ⟪P, g⟫ + φ x * ⟪R, g⟫ := by
  have hP := (Lp.memLp P).integrable_mul (Lp.memLp g)
  have hR := (Lp.memLp R).integrable_mul (Lp.memLp g)
  change Integrable (fun y => P y * g y) μ at hP
  change Integrable (fun y => R y * g y) μ at hR
  change (∫ y, K x y * g y ∂μ) = _
  calc
    _ = ∫ y, P y * g y + φ x * (R y * g y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrow] with y hy
      rw [hy]
      ring
    _ = _ := by
      rw [integral_add hP (hR.const_mul _), integral_const_mul,
        integral_real_mul, integral_real_mul]

private theorem affine_row_sq (K : Ω → Ω → ℝ) (P R : Lp ℝ 2 μ)
    (φ : Ω → ℝ) (x : Ω)
    (hrow : ∀ᵐ y ∂μ, K x y = P y + φ x * R y) :
    (∫ y, (K x y) ^ 2 ∂μ) =
      ‖P‖ ^ 2 + 2 * φ x * ⟪P, R⟫ + (φ x) ^ 2 * ‖R‖ ^ 2 := by
  have hP := (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable P)).mp (Lp.memLp P)
  have hR := (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable R)).mp (Lp.memLp R)
  have hPR := (Lp.memLp P).integrable_mul (Lp.memLp R)
  change Integrable (fun y => P y * R y) μ at hPR
  have hsum : Integrable (fun y => (P y) ^ 2 + (2 * φ x) * (P y * R y)) μ :=
    hP.add (hPR.const_mul _)
  calc
    _ = ∫ y, ((P y) ^ 2 + (2 * φ x) * (P y * R y)) +
        (φ x) ^ 2 * (R y) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrow] with y hy
      rw [hy]
      ring
    _ = _ := by
      rw [integral_add hsum (hR.const_mul _),
        integral_add hP (hPR.const_mul _), integral_const_mul, integral_const_mul,
        integral_real_sq, integral_real_sq, integral_real_mul]

variable [IsProbabilityMeasure μ]

/-- A supported direction orthogonal to the two affine row coefficients is
an actual null vector of the symmetric integral operator. -/
theorem affine_rows_operator_null
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (E : Set Ω) (P R : Lp ℝ 2 μ) (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hφB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C)
    (hrows : ∀ᵐ x ∂μ, x ∈ E → ∀ᵐ y ∂μ, K x y = P y + φ x * R y)
    (f : Lp ℝ 2 μ) (hsupport : ∀ᵐ x ∂μ, x ∉ E → f x = 0)
    (hmean : (∫ x, f x ∂μ) = 0) (hmoment : (∫ x, φ x * f x ∂μ) = 0) :
    operator K hB0 hK hB f = 0 := by
  have hfi := (Lp.memLp f).integrable (by norm_num)
  have hφfi := hfi.bdd_mul hφ hφB
  apply ext_inner_right ℝ
  intro g
  have hs := operator_symmetric K hB0 hK hB hsym f g
  change ⟪operator K hB0 hK hB f, g⟫ = ⟪f, operator K hB0 hK hB g⟫ at hs
  rw [hs, inner_zero_left, L2.inner_def]
  calc
    _ = ∫ x, f x * (⟪P, g⟫ + φ x * ⟪R, g⟫) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrows, hsupport, onL2_coe K hK hB g] with x hx hs hg
      change inner ℝ (f x) (onL2 K hK hB g x) = _
      rw [hg]
      simp only [RCLike.inner_apply, conj_trivial]
      by_cases he : x ∈ E
      · rw [affine_row_pairing K P R g φ x (hx he)]
        ring
      · rw [hs he]
        ring
    _ = (∫ x, f x ∂μ) * ⟪P, g⟫ + (∫ x, φ x * f x ∂μ) * ⟪R, g⟫ := by
      have heq : (fun x => f x * (⟪P, g⟫ + φ x * ⟪R, g⟫)) =
          (fun x => f x * ⟪P, g⟫ + (φ x * f x) * ⟪R, g⟫) := by
        funext x
        ring
      rw [heq, integral_add (hfi.mul_const _) (hφfi.mul_const _),
        integral_mul_const, integral_mul_const]
    _ = 0 := by rw [hmean, hmoment]; ring

/-- The actual linear squared-kernel energy coefficient of a supported
orthogonal direction is the squared row slope times its quadratic moment. -/
theorem affine_rows_energy_coefficient
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (E : Set Ω) (P R : Lp ℝ 2 μ) (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hφB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C)
    (hrows : ∀ᵐ x ∂μ, x ∈ E → ∀ᵐ y ∂μ, K x y = P y + φ x * R y)
    (f : Lp ℝ 2 μ) (hsupport : ∀ᵐ x ∂μ, x ∉ E → f x = 0)
    (hmean : (∫ x, f x ∂μ) = 0) (hmoment : (∫ x, φ x * f x ∂μ) = 0) :
    (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 * f p.1 ∂μ.prod μ) =
      ‖R‖ ^ 2 * (∫ x, (φ x) ^ 2 * f x ∂μ) := by
  have hfi := (Lp.memLp f).integrable (by norm_num)
  have hφfi := hfi.bdd_mul hφ hφB
  have hφsqB : ∀ᵐ x ∂μ, ‖(φ x) ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [hφB] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hφsqfi := hfi.bdd_mul (hφ.pow 2) hφsqB
  change Integrable (fun x => (φ x) ^ 2 * f x) μ at hφsqfi
  have hKsqB : ∀ᵐ p ∂μ.prod μ, ‖(K p.1 p.2) ^ 2‖ ≤ B ^ 2 := by
    filter_upwards [hB] with p hp
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hi := (hfi.comp_fst μ).bdd_mul (hK.pow 2) hKsqB
  change Integrable (fun p : Ω × Ω => (K p.1 p.2) ^ 2 * f p.1) (μ.prod μ) at hi
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, (‖P‖ ^ 2 + 2 * φ x * ⟪P, R⟫ + (φ x) ^ 2 * ‖R‖ ^ 2) * f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrows, hsupport] with x hx hs
      rw [integral_mul_const]
      by_cases he : x ∈ E
      · rw [affine_row_sq K P R φ x (hx he)]
      · rw [hs he]
        ring
    _ = ‖P‖ ^ 2 * (∫ x, f x ∂μ) +
        (2 * ⟪P, R⟫) * (∫ x, φ x * f x ∂μ) +
        ‖R‖ ^ 2 * (∫ x, (φ x) ^ 2 * f x ∂μ) := by
      have heq : (fun x => (‖P‖ ^ 2 + 2 * φ x * ⟪P, R⟫ +
          (φ x) ^ 2 * ‖R‖ ^ 2) * f x) =
          (fun x => (‖P‖ ^ 2 * f x + (2 * ⟪P, R⟫) * (φ x * f x)) +
            ‖R‖ ^ 2 * ((φ x) ^ 2 * f x)) := by
        funext x
        ring
      have hsum : Integrable
          (fun x => ‖P‖ ^ 2 * f x + (2 * ⟪P, R⟫) * (φ x * f x)) μ :=
        (hfi.const_mul _).add (hφfi.const_mul _)
      rw [heq, integral_add hsum (hφsqfi.const_mul _),
        integral_add (hfi.const_mul _) (hφfi.const_mul _), integral_const_mul,
        integral_const_mul, integral_const_mul]
    _ = _ := by rw [hmean, hmoment]; ring

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ] [MeasurableEq Ω]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Actual maximum-energy selection rules out a positive quadratic moment
on a nonconstant affine row block. The null vector is derived from its rows. -/
theorem FullStationaryClass.affine_rows_quadratic_moment_eq_zero_of_strict_gap
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmax : ∀ V : Model Ω μ, FullStationaryClass d c V m →
      stationaryEnergy V m ≤ stationaryEnergy W m)
    (E : Set Ω) (P R : Lp ℝ 2 μ) (hR : R ≠ 0) (φ : Ω → ℝ)
    (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hφB : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C)
    (hrows : ∀ᵐ x ∂μ, x ∈ E → ∀ᵐ y ∂μ,
      shiftedKernel W m x y = P y + φ x * R y)
    (f : Lp ℝ 2 μ) (hf : f ∈ KernelOperator.boundedL2Submodule μ)
    (hsupport : ∀ᵐ x ∂μ, x ∉ E → f x = 0)
    (hmean : (∫ x, f x ∂μ) = 0) (hmoment : (∫ x, φ x * f x ∂μ) = 0) :
    (∫ x, (φ x) ^ 2 * f x ∂μ) = 0 := by
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hnull : shiftedOperator W m f = 0 :=
    KernelOperator.affine_rows_operator_null (shiftedKernel W m) (by positivity)
      (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
      E P R φ hφ hφB hrows f hsupport hmean hmoment
  have hzero := hW.selected_energy_null_vector_first_variation_of_strict_gap
    hd hgap hmax f hf hnull
  rw [KernelOperator.affine_rows_energy_coefficient (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    E P R φ hφ hφB hrows f hsupport hmean hmoment] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hR))

end Erdos1017.CappedModel
