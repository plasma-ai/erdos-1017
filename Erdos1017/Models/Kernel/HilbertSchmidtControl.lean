module

public import Erdos1017.Models.Kernel.SpectralKernelPairing

/-!
# Operator-norm control of kernel L2 distance

For kernels with absolutely summable spectral representations, possibly in
different eigenbases, the operator norm controls the squared L2 distance of the
kernels, and bounded nonnegative symmetric kernels with finite positive spectral
rank satisfy this operator-to-L2 estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Products of bounded measurable kernels are integrable on the probability
product space. -/
theorem integrable_kernel_product
    (K L : Ω → Ω → ℝ) {B C : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ C) :
    Integrable (fun z : Ω × Ω => K z.1 z.2 * L z.1 z.2) (μ.prod μ) := by
  apply (show MemLp (fun z : Ω × Ω => K z.1 z.2 * L z.1 z.2) 1 (μ.prod μ) from
    MemLp.of_bound (hK.mul hL) (B * C) ?_).integrable le_rfl
  filter_upwards [hB, hC] with z hb hc
  rw [norm_mul]
  exact mul_le_mul hb hc (norm_nonneg _) hB0

/-- Operator-norm control of the squared L2 distance between actual kernels
with absolutely summable spectral representations. The two kernels may use
different eigenbases. -/
theorem integral_sq_sub_le_operator_mul_spectral_sums [Countable ι] [Countable κ]
    (K L : Ω → Ω → ℝ) {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ C)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (c : HilbertBasis κ ℝ (Lp ℝ 2 μ)) (u : κ → ℝ)
    (ht : Summable (fun i => |t i|)) (hu : Summable (fun i => |u i|))
    (hKseries : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ∑' i, t i * b i z.1 * b i z.2)
    (hLseries : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = ∑' i, u i * c i z.1 * c i z.2) :
    (∫ z : Ω × Ω, (K z.1 z.2 - L z.1 z.2) ^ 2 ∂μ.prod μ) ≤
      ‖operator K hB0 hK hB - operator L hC0 hL hC‖ *
        ((∑' i, |t i|) + ∑' i, |u i|) := by
  let H := fun x y => K x y - L x y
  have hH := hK.sub hL
  have hD := kernel_sub_bound hB hC
  have hD0 := add_nonneg hB0 hC0
  have hHK := integrable_kernel_product H K hD0 hH hK hD hB
  have hHL := integrable_kernel_product H L hD0 hH hL hD hC
  have hpk := norm_integral_spectral_pairing_le H K hD0 hH hD b t ht hKseries
  have hpl := norm_integral_spectral_pairing_le H L hD0 hH hD c u hu hLseries
  calc
    (∫ z : Ω × Ω, (K z.1 z.2 - L z.1 z.2) ^ 2 ∂μ.prod μ) =
        (∫ z : Ω × Ω, H z.1 z.2 * K z.1 z.2 ∂μ.prod μ) -
          ∫ z : Ω × Ω, H z.1 z.2 * L z.1 z.2 ∂μ.prod μ := by
      rw [← integral_sub hHK hHL]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by dsimp [H]; ring)
    _ ≤ ‖∫ z : Ω × Ω, H z.1 z.2 * K z.1 z.2 ∂μ.prod μ‖ +
        ‖∫ z : Ω × Ω, H z.1 z.2 * L z.1 z.2 ∂μ.prod μ‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      linarith [le_abs_self (∫ z : Ω × Ω, H z.1 z.2 * K z.1 z.2 ∂μ.prod μ),
        neg_le_abs (∫ z : Ω × Ω, H z.1 z.2 * L z.1 z.2 ∂μ.prod μ)]
    _ ≤ ‖operator H hD0 hH hD‖ * (∑' i, |t i|) +
        ‖operator H hD0 hH hD‖ * ∑' i, |u i| := add_le_add hpk hpl
    _ = ‖operator K hB0 hK hB - operator L hC0 hL hC‖ *
        ((∑' i, |t i|) + ∑' i, |u i|) := by
      rw [operator_sub K L hB0 hC0 hK hL hB hC]
      ring

/-- Bounded nonnegative symmetric kernels with finite positive spectral
rank satisfy the operator-to-L2 estimate from stabilization. Absolute
summability and the actual kernel series are constructed from their
eigenfunction equations; neither is supplied as an interpolation hypothesis. -/
theorem bounded_finite_positive_rank_hilbert_schmidt_control [Countable ι] [Countable κ]
    (K L : Ω → Ω → ℝ) {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ C)
    (hK0 : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hL0 : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z.1 z.2)
    (hKsym : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (hLsym : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = L z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (c : HilbertBasis κ ℝ (Lp ℝ 2 μ)) (u : κ → ℝ)
    (hKeigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (hLeigen : ∀ i, operator L hC0 hL hC (c i) = u i • c i)
    (s : Finset ι) (r : Finset κ)
    (hKinside : ∀ i ∈ s, 0 < t i) (hKoutside : ∀ i ∉ s, t i ≤ 0)
    (hLinside : ∀ i ∈ r, 0 < u i) (hLoutside : ∀ i ∉ r, u i ≤ 0) :
    (∫ z : Ω × Ω, (K z.1 z.2 - L z.1 z.2) ^ 2 ∂μ.prod μ) ≤
      ‖operator K hB0 hK hB - operator L hC0 hL hC‖ *
        ((∑' i, |t i|) + ∑' i, |u i|) := by
  obtain ⟨F, hF, hFR, hFcoord, hFrep⟩ := exists_bounded_spectral_feature
    K hB0 hK hB hK0 hKsym b t hKeigen s hKinside hKoutside
  obtain ⟨G, hG, hGR, hGcoord, hGrep⟩ := exists_bounded_spectral_feature
    L hC0 hL hC hL0 hLsym c u hLeigen r hLinside hLoutside
  exact integral_sq_sub_le_operator_mul_spectral_sums K L hB0 hC0 hK hL hB hC b t c u
    (summable_abs_eigenvalues_of_feature b t F _ hFR hFcoord)
    (summable_abs_eigenvalues_of_feature c u G _ hGR hGcoord)
    (spectral_series_of_feature K b t F hFcoord hFrep)
    (spectral_series_of_feature L c u G hGcoord hGrep)

end Erdos1017.KernelOperator
