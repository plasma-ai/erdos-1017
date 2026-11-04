module

public import Erdos1017.SelectedModel.Structure.IntegrableReturnNull
public import Erdos1017.SelectedModel.FullDiffuseCompletion

/-!
# Endpoint density sign for integrable directions

In a strict-gap optimum an integrable mean-zero null row must be degree tangent,
so nonnegative shifted energy and nonzero degree slope exclude every interior
density return, and the endpoint density cannot lie opposite to the degree slope
(`endpoint_density_sign`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An actual null integral row annihilates every integrable mixed test.
Fubini is justified by the bounded kernel and the two L¹ inputs. -/
theorem kernelPairing_eq_zero_of_applyKernel_eq_zero
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hnull : ∀ᵐ x ∂μ, applyKernel (μ := μ) K f x = 0) :
    kernelPairing (μ := μ) K f g = 0 := by
  rw [kernelPairing, integral_prod _ (integrable_kernel_bilinear hK hB hf hg)]
  calc
    _ = ∫ x, applyKernel (μ := μ) K f x * g x ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change (∫ y, (K x y * f y) * g x ∂μ) = (∫ y, K x y * f y ∂μ) * g x
      exact integral_mul_const _ _
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hnull] with x hx
      simp only [hx, zero_mul, Pi.zero_apply]

end Erdos1017.KernelOperator

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- In the same actual strict-gap optimum, an integrable mean-zero null
row must be degree tangent. Otherwise it corrects an actual positive
direction to an L¹ tangent direction with the same positive energy,
contradicting the proved extension of actual bounded weight variation. -/
theorem FullStationaryClass.integrable_null_degree_eq_zero
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hnull : ∀ᵐ x ∂μ, KernelOperator.applyKernel (μ := μ) (shiftedKernel W m) v x = 0) :
    (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) = 0 := by
  by_contra hL
  obtain ⟨u, _, hpos⟩ := hW.exists_transverse_positive_direction hd hgap
  let f := Variation.directionToL2 u
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hf : Integrable (f : Ω → ℝ) μ := (Lp.memLp f).integrable (by norm_num)
  have hfm : (∫ x, f x ∂μ) = 0 := Variation.direction_integral_zero u
  obtain ⟨C, _, hgBound⟩ :=
    (show g ∈ KernelOperator.boundedL2Submodule μ from KernelOperator.operator_range_bounded _ _ _ _ _)
  let a := (∫ x, g x * f x ∂μ) / (∫ x, g x * v x ∂μ)
  have had : a * (∫ x, g x * v x ∂μ) = ∫ x, g x * f x ∂μ := div_mul_cancel₀ _ hL
  have hz : Integrable (fun x => f x - a * v x) μ := hf.sub (hv.const_mul a)
  have hzm : (∫ x, f x - a * v x ∂μ) = 0 := by
    rw [integral_sub hf (hv.const_mul a), integral_const_mul, hfm, hmean, mul_zero, sub_self]
  have hzd : (∫ x, g x * (f x - a * v x) ∂μ) = 0 := by
    have heq : (fun x => g x * (f x - a * v x)) =
        (fun x => g x * f x - a * (g x * v x)) := by funext x; ring
    rw [heq, integral_sub
      (KernelOperator.integrable_bounded_mul (Lp.memLp g).aestronglyMeasurable hgBound hf)
      ((KernelOperator.integrable_bounded_mul (Lp.memLp g).aestronglyMeasurable hgBound hv).const_mul a),
      integral_const_mul, had, sub_self]
  have hnonpos := hW.integrable_tangent_nonpositive_of_strict_gap hd hgap
    (fun x => f x - a * v x) hz hzm hzd
  have hsym : ∀ᵐ p ∂μ.prod μ, shiftedKernel W m p.1 p.2 = shiftedKernel W m p.2 p.1 := by
    filter_upwards [shiftedMoment_symm W m] with p hp
    exact hp.symm
  have hvv := KernelOperator.kernelPairing_eq_zero_of_applyKernel_eq_zero _
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) v v hv hv hnull
  have hvf := KernelOperator.kernelPairing_eq_zero_of_applyKernel_eq_zero _
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m) v f hv hf hnull
  have hfv : KernelOperator.kernelPairing (μ := μ) (shiftedKernel W m) f v = 0 :=
    (KernelOperator.kernelPairing_symm _ hsym f v).trans hvf
  change KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v = 0 at hvv
  rw [KernelOperator.kernelEnergy_sub_mul _ (shiftedKernel_measurable W m)
    (shiftedKernel_bound W m) hsym f v hf hv a, hfv, hvv] at hnonpos
  have henergy : Variation.weightSecondVariation (shiftedOperator W m) u u =
      KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) f := by
    change ⟪shiftedOperator W m f, f⟫ = _
    exact KernelOperator.operator_inner _ _ _ _ f f
  rw [henergy] at hpos
  linarith

/-- Nonnegative original shifted energy and nonzero original degree slope
exclude every interior density return, including the zero-energy case. -/
theorem FullStationaryClass.no_interior_density_return
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (hL : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) ≠ 0)
    (hE : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    density (integrableTilt W v hv hmean hbelow t ⟨ht.1.le, ht.2.le⟩) ≠ d := by
  intro hreturn
  rcases hE.eq_or_lt with hz | hpos
  · exact hL (hW.integrable_null_degree_eq_zero hd hgap v hv hmean
      (hW.integrable_return_null v hv hmean hbelow hL hz.symm t ht hreturn))
  · exact hW.no_density_return_of_positive_energy v hv hmean hbelow hpos t
      ⟨ht.1.le, ht.2.le⟩ ht.1 hreturn

/-- The actual endpoint density cannot lie opposite to the original
nonzero degree slope. All affine laws retain the unchanged full-feasible
dual; this theorem constructs no physical flow or recovery coupling. -/
theorem FullStationaryClass.endpoint_density_sign
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (v : Ω → ℝ) (hv : Integrable v μ) (hmean : (∫ x, v x ∂μ) = 0)
    (hbelow : ∀ᵐ x ∂μ, -1 ≤ v x)
    (hL : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) ≠ 0)
    (hE : 0 ≤ KernelOperator.kernelEnergy (μ := μ) (shiftedKernel W m) v) :
    0 ≤ (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ) *
      (density (integrableTilt W v hv hmean hbelow 1 ⟨by norm_num, le_rfl⟩) - d) := by
  let L := ∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * v x ∂μ
  let A := KernelOperator.kernelEnergy (μ := μ) (adjacencyKernel W) v / 2
  have hpoly (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      density (integrableTilt W v hv hmean hbelow t ht) = d + t * L + t ^ 2 * A := by
    rw [density_integrableTilt, hW.density_eq]
    dsimp only [L, A]
    ring
  by_contra hnot
  have hopp : L * (L + A) < 0 := by
    have h := lt_of_not_ge hnot
    rw [hpoly 1 ⟨by norm_num, le_rfl⟩] at h
    change L * (d + 1 * L + 1 ^ 2 * A - d) < 0 at h
    nlinarith
  obtain ⟨t, ht, hzero⟩ := exists_quadratic_density_return L A hopp
  have heq := hpoly t ⟨ht.1.le, ht.2.le⟩
  apply hW.no_interior_density_return hd hgap v hv hmean hbelow hL hE t ht
  linarith

end Erdos1017.CappedModel
