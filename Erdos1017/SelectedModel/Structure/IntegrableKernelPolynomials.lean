module

public import Erdos1017.SelectedModel.Structure.IntegrableDegreeCone

/-!
# Kernel energy polynomials for integrable weights

The unit weight has the original unhalved pair integral, pairing a unit weight
against an integrable function is its pairing with the row integral, bounded
kernels have the exact affine-weight energy polynomial for every integrable
direction, and a scalar kernel shift commutes with the energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The unit weight has the actual original unhalved pair integral. -/
theorem kernelEnergy_one (K : Ω → Ω → ℝ) :
    kernelEnergy (μ := μ) K (fun _ => 1) = ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ := by
  simp only [kernelEnergy, mul_one]

/-- Pairing a unit weight against an integrable function is exactly its
pairing with the original physical row integral. -/
theorem kernelPairing_one_eq_row
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    kernelPairing (μ := μ) K (fun _ => 1) f = ∫ x, (∫ y, K x y ∂μ) * f x ∂μ := by
  rw [kernelPairing, integral_prod _ (integrable_kernel_bilinear hK hB (integrable_const 1) hf)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [mul_one, integral_mul_const])

/-- Actual bounded kernels have the exact affine-weight energy polynomial
for every integrable direction, with no L² or bounded-input assumption. -/
theorem kernelEnergy_one_add_mul
    (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (f : Ω → ℝ) (hf : Integrable f μ) (t : ℝ) :
    kernelEnergy (μ := μ) K (fun x => 1 + t * f x) =
      kernelEnergy (μ := μ) K (fun _ => 1) +
        2 * t * kernelPairing (μ := μ) K (fun _ => 1) f +
          t ^ 2 * kernelEnergy (μ := μ) K f := by
  have h := kernelEnergy_sub_mul K hK hB hsym (fun _ => 1) f (integrable_const 1) hf (-t)
  simpa only [neg_mul, sub_neg_eq_add, neg_sq, mul_neg] using h

/-- An actual scalar kernel shift commutes with the integrable physical
energy; all integrals split using actual L¹ bilinear integrability. -/
theorem kernelEnergy_sub_kernel
    (K L : Ω → Ω → ℝ) {B C : ℝ}
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun p : Ω × Ω => L p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hC : ∀ᵐ p ∂μ.prod μ, ‖L p.1 p.2‖ ≤ C)
    (f : Ω → ℝ) (hf : Integrable f μ) (m : ℝ) :
    kernelEnergy (μ := μ) (fun x y => K x y - m * L x y) f =
      kernelEnergy (μ := μ) K f - m * kernelEnergy (μ := μ) L f := by
  have heq : (fun p : Ω × Ω => (K p.1 p.2 - m * L p.1 p.2) * f p.2 * f p.1) =
      (fun p => K p.1 p.2 * f p.2 * f p.1 - m * (L p.1 p.2 * f p.2 * f p.1)) := by
    funext p
    ring
  rw [kernelEnergy, heq, integral_sub (integrable_kernel_bilinear hK hB hf hf)
    ((integrable_kernel_bilinear hL hC hf hf).const_mul m), integral_const_mul]
  rfl

end Erdos1017.KernelOperator
