module

public import Erdos1017.Exclusions.Common.KernelCubicIntegration

/-!
# Signed copy-row trace bounds

The raw copy integral keeps its linear body moment with a signed coefficient,
and the orthogonal cubic estimate controls the copied-row inequality even when
that coefficient is negative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The raw copy integral keeps its linear body moment and permits a signed
coefficient. No comparison of that coefficient with zero is required. -/
theorem signed_integrated_copy_row_bound (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hsym : ∀ x y, K x y = K y x)
    (a g : ℝ)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1)) :
    a * (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      g * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤
      2 * (∫ p : Ω × Ω, J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ) := by
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  have hKl : MemLp (fun p : Ω × Ω => K p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hK.aestronglyMeasurable 1 (Eventually.of_forall (fun p => hKB p.1 p.2))
  have hJK := measurable_composedKernel (μ := μ) J K hJ hK
  have hpair : Integrable (fun p : Ω × Ω =>
      K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (hK.mul hJK).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hKB p.1 p.2)
          (composedKernel_bound (μ := μ) J K 1 1 (by norm_num) hJB hKB p.1 p.2)
          (norm_nonneg _) zero_le_one))
  have hpairSwap : Integrable (fun p : Ω × Ω =>
      K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1) (μ.prod μ) := by
    have hi := MeasurePreserving.integrable_comp_of_integrable
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)) hpair
    convert hi using 1
    funext p
    change K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1 =
      K p.2 p.1 * composedKernel (μ := μ) J K p.2 p.1
    rw [hsym p.2 p.1]
  have hiL : Integrable (fun p : Ω × Ω => a * (K p.1 p.2) ^ 2 + g * K p.1 p.2)
      (μ.prod μ) := (hKl.integrable_sq.const_mul a).add
        ((hKl.integrable (by norm_num)).const_mul g)
  have hiR : Integrable (fun p : Ω × Ω => K p.1 p.2 *
      (composedKernel (μ := μ) J K p.1 p.2 + composedKernel (μ := μ) J K p.2 p.1))
      (μ.prod μ) := by
    have hi : Integrable (fun p : Ω × Ω =>
        K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2 +
        K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1) (μ.prod μ) :=
      hpair.add hpairSwap
    simpa only [mul_add] using hi
  have hbound := integral_mono_ae hiL hiR hrow
  have hswap : (∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) J K p.2 p.1 ∂μ.prod μ) =
      ∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2 ∂μ.prod μ := by
    calc
      _ = ∫ p : Ω × Ω, K p.2 p.1 * composedKernel (μ := μ) J K p.2 p.1 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by dsimp only; rw [hsym p.1 p.2])
      _ = _ := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).integral_comp
        (MeasurableEquiv.prodComm (α := Ω) (β := Ω)).measurableEmbedding
        (fun p : Ω × Ω => K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2)
  rw [integral_add (hKl.integrable_sq.const_mul a)
    ((hKl.integrable (by norm_num)).const_mul g), integral_const_mul, integral_const_mul] at hbound
  simp_rw [mul_add] at hbound
  rw [integral_add hpair hpairSwap, hswap,
    integral_mul_composed_swap K J hK hJ hKB hJB hsym] at hbound
  linarith only [hbound]

/-- The orthogonal cubic estimate controls the raw copied-row inequality
even when the coefficient of the linear body moment is negative. -/
theorem signed_copy_row_trace_bound [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hsym : ∀ x y, K x y = K y x)
    (a g : ℝ)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1)) :
    (a - Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ))) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
      g * (∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ) ≤ 0 := by
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  have hcopy := signed_integrated_copy_row_bound K J hK hJ hK01 hJB hsym a g hrow
  have hsharp := orthogonal_composed_pairing_sq_le K J hK hJ 1 1 zero_le_one hKB hJB
    (Eventually.of_forall (fun p => hsym p.1 p.2)) hpositive horthogonal
  have hH : 0 ≤ ∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun p => sq_nonneg _)
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
  have hsharp' :
      (2 * (∫ p : Ω × Ω, J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ)) ^ 2 ≤
      (Real.sqrt (2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ)) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)) ^ 2 := by
    simpa only [mul_pow, hsqrt] using hsharp
  have hupper := le_of_sq_le_sq hsharp' (mul_nonneg (Real.sqrt_nonneg _) hpositive.le)
  nlinarith only [hcopy, hupper]

end Erdos1017.KernelOperator
