module

public import Erdos1017.SelectedModel.Structure.L1KernelTangent

/-!
# Reverse Cauchy on integrable degree cones

This module defines the unhalved physical kernel pairing `kernelPairing` and
shows that the integrable tangent inequality gives reverse Cauchy on both strict
degree cones, at the strict-gap full optimum for integrable mean-zero inputs
without boundedness or `L²` membership.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual unhalved physical kernel pairing, with the first input on
the second coordinate of the kernel. -/
def kernelPairing (K : Ω → Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  ∫ p : Ω × Ω, K p.1 p.2 * f p.2 * g p.1 ∂μ.prod μ

/-- Actual product-AE kernel symmetry gives mixed-pairing symmetry. -/
theorem kernelPairing_symm (K : Ω → Ω → ℝ)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1) (f g : Ω → ℝ) :
    kernelPairing (μ := μ) K f g = kernelPairing (μ := μ) K g f := by
  rw [kernelPairing, kernelPairing,
    ← integral_prod_swap (fun p : Ω × Ω => K p.1 p.2 * g p.2 * f p.1)]
  apply integral_congr_ae
  filter_upwards [hsym] with p hp
  change K p.1 p.2 * f p.2 * g p.1 = K p.2 p.1 * g p.1 * f p.2
  rw [hp]
  ring

/-- Actual L¹ bilinear integrability justifies the quadratic expansion of
the degree-corrected difference, with all unhalved factors explicit. -/
theorem kernelEnergy_sub_mul
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (t : ℝ) :
    kernelEnergy (μ := μ) K (fun x => f x - t * g x) =
      kernelEnergy (μ := μ) K f - 2 * t * kernelPairing (μ := μ) K f g +
        t ^ 2 * kernelEnergy (μ := μ) K g := by
  have hff := integrable_kernel_bilinear hK hB hf hf
  have hgf := integrable_kernel_bilinear hK hB hg hf
  have hfg := integrable_kernel_bilinear hK hB hf hg
  have hgg := integrable_kernel_bilinear hK hB hg hg
  have heq : (fun p : Ω × Ω => K p.1 p.2 * (f p.2 - t * g p.2) * (f p.1 - t * g p.1)) =
      (fun p => (K p.1 p.2 * f p.2 * f p.1 - t * (K p.1 p.2 * g p.2 * f p.1)) -
        t * (K p.1 p.2 * f p.2 * g p.1) + t ^ 2 * (K p.1 p.2 * g p.2 * g p.1)) := by
    funext p
    ring
  have hi : Integrable (fun p : Ω × Ω =>
      K p.1 p.2 * f p.2 * f p.1 - t * (K p.1 p.2 * g p.2 * f p.1)) (μ.prod μ) :=
    hff.sub (hgf.const_mul t)
  have hj : Integrable (fun p : Ω × Ω =>
      (K p.1 p.2 * f p.2 * f p.1 - t * (K p.1 p.2 * g p.2 * f p.1)) -
        t * (K p.1 p.2 * f p.2 * g p.1)) (μ.prod μ) := hi.sub (hfg.const_mul t)
  rw [kernelEnergy, heq, integral_add hj (hgg.const_mul (t ^ 2)),
    integral_sub hi (hfg.const_mul t), integral_sub hff (hgf.const_mul t)]
  simp only [integral_const_mul]
  change kernelEnergy (μ := μ) K f - t * kernelPairing (μ := μ) K g f -
      t * kernelPairing (μ := μ) K f g + t ^ 2 * kernelEnergy (μ := μ) K g = _
  rw [kernelPairing_symm K hsym g f]
  ring

/-- The actual integrable tangent inequality gives reverse Cauchy on both
strict degree cones. Neither input needs boundedness or L² membership. -/
theorem integrable_degree_cone_reverse_cauchy
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ)
    {Cg : ℝ} (hgBound : ∀ᵐ a ∂μ, ‖g a‖ ≤ Cg)
    (hnonpos : ∀ f : Ω → ℝ, Integrable f μ → (∫ a, f a ∂μ) = 0 →
      (∫ a, g a * f a ∂μ) = 0 → kernelEnergy (μ := μ) K f ≤ 0)
    (x y : Ω → ℝ) (hx : Integrable x μ) (hy : Integrable y μ)
    (hxm : (∫ a, x a ∂μ) = 0) (hym : (∫ a, y a ∂μ) = 0)
    (hqx : 0 ≤ kernelEnergy (μ := μ) K x) (hqy : 0 ≤ kernelEnergy (μ := μ) K y)
    (hdegree : 0 < (∫ a, g a * x a ∂μ) * (∫ a, g a * y a ∂μ)) :
    0 ≤ kernelPairing (μ := μ) K x y ∧
      kernelEnergy (μ := μ) K x * kernelEnergy (μ := μ) K y ≤
        kernelPairing (μ := μ) K x y ^ 2 := by
  let t := (∫ a, g a * x a ∂μ) / (∫ a, g a * y a ∂μ)
  have ht : 0 < t := div_pos_iff.mpr (mul_pos_iff.mp hdegree)
  have hyne : (∫ a, g a * y a ∂μ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdegree
    exact (lt_irrefl 0) hdegree
  have htd : t * (∫ a, g a * y a ∂μ) = ∫ a, g a * x a ∂μ := div_mul_cancel₀ _ hyne
  have hf : Integrable (fun a => x a - t * y a) μ := hx.sub (hy.const_mul t)
  have hmean : (∫ a, x a - t * y a ∂μ) = 0 := by
    rw [integral_sub hx (hy.const_mul t), integral_const_mul, hxm, hym, mul_zero, sub_self]
  have hdeg : (∫ a, g a * (x a - t * y a) ∂μ) = 0 := by
    have heq : (fun a => g a * (x a - t * y a)) =
        (fun a => g a * x a - t * (g a * y a)) := by funext a; ring
    rw [heq, integral_sub (integrable_bounded_mul hg hgBound hx)
      ((integrable_bounded_mul hg hgBound hy).const_mul t), integral_const_mul, htd, sub_self]
  have henergy := hnonpos (fun a => x a - t * y a) hf hmean hdeg
  rw [kernelEnergy_sub_mul K hK hB hsym x y hx hy t] at henergy
  let qx := kernelEnergy (μ := μ) K x
  let qy := kernelEnergy (μ := μ) K y
  let b := kernelPairing (μ := μ) K x y
  have hbound : qx + t ^ 2 * qy ≤ 2 * t * b := by
    change qx - 2 * t * b + t ^ 2 * qy ≤ 0 at henergy
    linarith
  have hty : 0 ≤ t ^ 2 * qy := mul_nonneg (sq_nonneg t) hqy
  have hcross : 0 ≤ b := by nlinarith
  refine ⟨hcross, ?_⟩
  have hsq : (qx + t ^ 2 * qy) ^ 2 ≤ (2 * t * b) ^ 2 :=
    (sq_le_sq₀ (add_nonneg hqx hty) (by positivity)).mpr hbound
  have hscaled : t ^ 2 * (qx * qy) ≤ t ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (qx - t ^ 2 * qy)]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp hscaled

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The same original strict-gap full optimum satisfies reverse Cauchy for
actual integrable mean-zero inputs in either strict original-degree cone.
No bounded-input, L², minimum-multiplier or flow-certificate premise is used. -/
theorem FullStationaryClass.integrable_degree_cone_reverse_cauchy
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (x y : Ω → ℝ) (hx : Integrable x μ) (hy : Integrable y μ)
    (hxm : (∫ a, x a ∂μ) = 0) (hym : (∫ a, y a ∂μ) = 0)
    (hqx : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) x)
    (hqy : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) y)
    (hdegree : 0 < (∫ a, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) a * x a ∂μ) *
      (∫ a, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) a * y a ∂μ)) :
    0 ≤ KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) x y ∧
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) x *
        KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) y ≤
          KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) x y ^ 2 := by
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hgBound : g ∈ KernelOperator.boundedL2Submodule μ :=
    KernelOperator.operator_range_bounded _ _ _ _ _
  obtain ⟨Cg, _, hgBound⟩ := hgBound
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  exact KernelOperator.integrable_degree_cone_reverse_cauchy (shiftedKernel W m)
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) hsym
    (g : Ω → ℝ) (Lp.memLp g).aestronglyMeasurable hgBound
    (hW.integrable_tangent_nonpositive_of_strict_gap hd hgap)
    x y hx hy hxm hym hqx hqy hdegree

end Erdos1017.CappedModel
