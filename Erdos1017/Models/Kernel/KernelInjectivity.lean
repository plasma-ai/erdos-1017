module

public import Erdos1017.Models.Kernel.KernelSpectralPart

/-!
# Kernels determined by their operators

Continuous linear operators agreeing on a Hilbert basis agree everywhere, and a
bounded measurable kernel with zero integral operator vanishes almost
everywhere, with countability making the row tests simultaneous.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

/-- Continuous linear operators agreeing on a Hilbert basis agree everywhere. -/
theorem operator_eq_of_hilbertBasis {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis ι ℝ E) (T S : E →L[ℝ] E)
    (h : ∀ i, T (b i) = S (b i)) : T = S := by
  let L := T - S
  have hspan : Submodule.span ℝ (Set.range b) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change T (b i) - S (b i) = 0
    rw [h, sub_self]
  have htop : (⊤ : Submodule ℝ E) ≤ L.ker := by
    rw [← b.dense_span]
    exact (Submodule.span ℝ (Set.range b)).topologicalClosure_minimal hspan L.isClosed_ker
  apply ContinuousLinearMap.ext
  intro x
  exact sub_eq_zero.mp (htop (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ E)))

/-- A bounded measurable kernel with zero integral operator vanishes almost
everywhere. Countability makes the row tests simultaneous. -/
theorem kernel_ae_zero_of_operator_eq_zero
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Countable ι] (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hzero : operator K hB0 hK hB = 0) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = 0 := by
  have hcol (i : ι) : ∀ᵐ x ∂μ, applyKernel (μ := μ) K (b i) x = 0 := by
    have h := (onL2_coe K hK hB (b i)).symm
    have hz : onL2 K hK hB (b i) = 0 := by
      change operator K hB0 hK hB (b i) = 0
      rw [hzero]
      rfl
    rw [hz] at h
    exact h.trans (Lp.coeFn_zero ℝ 2 μ)
  have hall : ∀ᵐ x ∂μ, ∀ i, applyKernel (μ := μ) K (b i) x = 0 := ae_all_iff.mpr hcol
  have hrows : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, K x y = 0 := by
    filter_upwards [ae_memLp_row hK hB, hall] with x hx hi
    have hz : hx.toLp (K x) = 0 := by
      apply b.repr.injective
      apply lp.ext
      funext i
      rw [b.repr_apply_apply]
      have heq := hi i
      rw [applyKernel_eq_inner hx] at heq
      simpa using heq
    have hc := hx.coeFn_toLp.symm
    rw [hz] at hc
    exact hc.trans (Lp.coeFn_zero ℝ 2 μ)
  have hint : Integrable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ) :=
    (show MemLp (fun z : Ω × Ω => K z.1 z.2) 1 (μ.prod μ) from
      MemLp.of_bound hK B hB).integrable le_rfl
  have hnorm : (∫ z : Ω × Ω, ‖K z.1 z.2‖ ∂μ.prod μ) = 0 := by
    rw [integral_prod _ hint.norm]
    apply integral_eq_zero_of_ae
    filter_upwards [hrows] with x hx
    apply integral_eq_zero_of_ae
    exact hx.mono (fun y hy => by simp [hy])
  have hz := (integral_eq_zero_iff_of_nonneg (fun z : Ω × Ω => norm_nonneg (K z.1 z.2)) hint.norm).mp hnorm
  exact hz.mono (fun z hz => norm_eq_zero.mp hz)

end Erdos1017.KernelOperator
