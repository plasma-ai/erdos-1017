module

public import Erdos1017.Models.Kernel.HilbertSchmidtControl
public import Erdos1017.Models.Capped.CappedSelectedTrace

/-!
# Squared L2 convergence from operator convergence

Finite positive rank supplies the spectral representations and absolute sums
needed to compare two bounded nonnegative symmetric kernels, so uniformly
bounded positive spectral rank upgrades operator convergence to convergence of
the squared kernel L2 difference.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Finite positive rank supplies the actual spectral representations and
absolute sums used to compare two bounded nonnegative symmetric kernels.
No eigenbasis, positive index set or kernel series is an input. -/
theorem integral_sq_sub_le_of_positive_rank
    (K L : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hKB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hLB : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hL0 : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z.1 z.2)
    (hKsym : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (hLsym : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = L z.2 z.1)
    (hKfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hKB)))
    (hLfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator L hB0 hL hLB)))
    (r : ℕ)
    (hKrank : Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hKB)) ≤ r)
    (hLrank : Module.finrank ℝ (positiveSpectralSubspace (operator L hB0 hL hLB)) ≤ r) :
    (∫ z : Ω × Ω, (K z.1 z.2 - L z.1 z.2) ^ 2 ∂μ.prod μ) ≤
      ‖operator K hB0 hK hKB - operator L hB0 hL hLB‖ * (4 * (r : ℝ) * B) := by
  classical
  let := hKfinite
  let := hLfinite
  obtain ⟨ι, hι, b, t, hKeigen⟩ := exists_countable_eigen_hilbertBasis (operator K hB0 hK hKB)
    (operator_isCompact K hB0 hK hKB) (operator_symmetric K hB0 hK hKB hKsym)
  obtain ⟨κ, hκ, c, u, hLeigen⟩ := exists_countable_eigen_hilbertBasis (operator L hB0 hL hLB)
    (operator_isCompact L hB0 hL hLB) (operator_symmetric L hB0 hL hLB hLsym)
  let := hι
  let := hκ
  have hpositiveK := finite_positive_basis_indices (operator K hB0 hK hKB) b t hKeigen
  have hpositiveL := finite_positive_basis_indices (operator L hB0 hL hLB) c u hLeigen
  let s := hpositiveK.toFinset
  let q := hpositiveL.toFinset
  have hKinside : ∀ i ∈ s, 0 < t i := fun i hi => hpositiveK.mem_toFinset.mp hi
  have hLinside : ∀ i ∈ q, 0 < u i := fun i hi => hpositiveL.mem_toFinset.mp hi
  have hKoutside : ∀ i ∉ s, t i ≤ 0 :=
    fun i hi => le_of_not_gt (fun h => hi (hpositiveK.mem_toFinset.mpr h))
  have hLoutside : ∀ i ∉ q, u i ≤ 0 :=
    fun i hi => le_of_not_gt (fun h => hi (hpositiveL.mem_toFinset.mpr h))
  have hcardK : s.card ≤ r :=
    (positive_basis_card_le_finrank (operator K hB0 hK hKB) b t hKeigen s hKinside).trans hKrank
  have hcardL : q.card ≤ r :=
    (positive_basis_card_le_finrank (operator L hB0 hL hLB) c u hLeigen q hLinside).trans hLrank
  have hsumK := (summable_spectral_abs_and_bound K hB0 hK hKB hK0 hKsym b t hKeigen s hKinside hKoutside).2
  have hsumL := (summable_spectral_abs_and_bound L hB0 hL hLB hL0 hLsym c u hLeigen q hLinside hLoutside).2
  have hcardK' : (s.card : ℝ) ≤ r := by exact_mod_cast hcardK
  have hcardL' : (q.card : ℝ) ≤ r := by exact_mod_cast hcardL
  have hboundK := mul_le_mul_of_nonneg_right hcardK' (show 0 ≤ 2 * B by positivity)
  have hboundL := mul_le_mul_of_nonneg_right hcardL' (show 0 ≤ 2 * B by positivity)
  have hsum : (∑' i, |t i|) + (∑' i, |u i|) ≤ 4 * (r : ℝ) * B := by
    nlinarith only [hsumK, hsumL, hboundK, hboundL]
  exact (bounded_finite_positive_rank_hilbert_schmidt_control K L hB0 hB0 hK hL hKB hLB
    hK0 hL0 hKsym hLsym b t c u hKeigen hLeigen s q hKinside hKoutside hLinside hLoutside).trans
    (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))

/-- Uniformly bounded positive spectral rank upgrades actual operator
convergence to convergence of the actual squared kernel-L2 difference. -/
theorem tendsto_integral_sq_sub_of_positive_rank
    (K : ℕ → Ω → Ω → ℝ) (L : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : ∀ n, AEStronglyMeasurable (fun z : Ω × Ω => K n z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hKB : ∀ n, ∀ᵐ z ∂μ.prod μ, ‖K n z.1 z.2‖ ≤ B)
    (hLB : ∀ᵐ z ∂μ.prod μ, ‖L z.1 z.2‖ ≤ B)
    (hK0 : ∀ n, ∀ᵐ z ∂μ.prod μ, 0 ≤ K n z.1 z.2)
    (hL0 : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z.1 z.2)
    (hKsym : ∀ n, ∀ᵐ z ∂μ.prod μ, K n z.1 z.2 = K n z.2 z.1)
    (hLsym : ∀ᵐ z ∂μ.prod μ, L z.1 z.2 = L z.2 z.1)
    (hKfinite : ∀ n, FiniteDimensional ℝ (positiveSpectralSubspace (operator (K n) hB0 (hK n) (hKB n))))
    (hLfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator L hB0 hL hLB)))
    (r : ℕ)
    (hKrank : ∀ n, Module.finrank ℝ (positiveSpectralSubspace (operator (K n) hB0 (hK n) (hKB n))) ≤ r)
    (hLrank : Module.finrank ℝ (positiveSpectralSubspace (operator L hB0 hL hLB)) ≤ r)
    (hop : Tendsto (fun n => ‖operator (K n) hB0 (hK n) (hKB n) - operator L hB0 hL hLB‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : Ω × Ω, (K n z.1 z.2 - L z.1 z.2) ^ 2 ∂μ.prod μ) atTop (𝓝 0) := by
  have hscaled : Tendsto (fun n =>
      ‖operator (K n) hB0 (hK n) (hKB n) - operator L hB0 hL hLB‖ * (4 * (r : ℝ) * B)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hop.mul_const (4 * (r : ℝ) * B)
  exact squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => integral_sq_sub_le_of_positive_rank (K n) L hB0 (hK n) hL (hKB n) hLB
      (hK0 n) hL0 (hKsym n) hLsym (hKfinite n) hLfinite r (hKrank n) hLrank) hscaled

end Erdos1017.KernelOperator
