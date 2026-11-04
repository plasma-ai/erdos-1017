module

public import Erdos1017.Exclusions.Common.KernelCompositionMoments

/-!
# Cubic pairing orthogonal to the kernel

With a Cauchy-Schwarz inequality for real `L²` functions, orthogonality to the
kernel removes the cubic spectral mean, leaving a composed-kernel pairing bound
with the sharp factor two.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Cauchy–Schwarz for actual real L² functions, with their original
square integrals on the right. -/
theorem integral_mul_sq_le (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hinner : ⟪F, G⟫ = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    change G x * F x = f x * g x
    change hg.toLp g x * hf.toLp f x = f x * g x
    rw [hx, hy, mul_comm]
  have hF : ‖F‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
    rw [← integral_L2_sq]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hG : ‖G‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
    rw [← integral_L2_sq]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  have h := real_inner_mul_inner_self_le F G
  rw [hinner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hF, hG] at h
  simpa only [pow_two] using h

/-- Orthogonality to the original kernel removes the cubic spectral mean.
The remaining genuine composed-kernel pairing has the sharp factor two. -/
theorem orthogonal_composed_pairing_sq_le
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (B C : ℝ) (hB0 : 0 ≤ B)
    (hKB : ∀ x y, ‖K x y‖ ≤ B) (hJC : ∀ x y, ‖J x y‖ ≤ C)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0) :
    (2 * (∫ p : Ω × Ω, J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ)) ^ 2 ≤
      2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) *
        (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ^ 2 := by
  let L := composedKernel (μ := μ) K K
  let Z := ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ
  let a := (∫ p : Ω × Ω, K p.1 p.2 * L p.1 p.2 ∂μ.prod μ) / Z
  have hL := measurable_composedKernel (μ := μ) K K hK hK
  have hLB : ∀ x y, ‖L x y‖ ≤ B * B :=
    composedKernel_bound (μ := μ) K K B B hB0 hKB hKB
  have hKlp : MemLp (fun p : Ω × Ω => K p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hK.aestronglyMeasurable B
      (Eventually.of_forall (fun p => hKB p.1 p.2))
  have hJlp : MemLp (fun p : Ω × Ω => J p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hJ.aestronglyMeasurable C
      (Eventually.of_forall (fun p => hJC p.1 p.2))
  have hLlp : MemLp (fun p : Ω × Ω => L p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hL.aestronglyMeasurable (B * B)
      (Eventually.of_forall (fun p => hLB p.1 p.2))
  have hRlp : MemLp (fun p : Ω × Ω => L p.1 p.2 - a * K p.1 p.2) 2 (μ.prod μ) :=
    hLlp.sub (hKlp.const_mul a)
  have hpair : (∫ p : Ω × Ω, J p.1 p.2 * (L p.1 p.2 - a * K p.1 p.2) ∂μ.prod μ) =
      ∫ p : Ω × Ω, J p.1 p.2 * L p.1 p.2 ∂μ.prod μ := by
    simp_rw [mul_sub, mul_left_comm (J _ _) a]
    have hiJL : Integrable (fun p : Ω × Ω => J p.1 p.2 * L p.1 p.2) (μ.prod μ) :=
      hJlp.integrable_mul hLlp
    have hiJK : Integrable (fun p : Ω × Ω => a * (J p.1 p.2 * K p.1 p.2))
        (μ.prod μ) := (hJlp.integrable_mul hKlp).const_mul a
    rw [integral_sub hiJL hiJK,
      integral_const_mul, horthogonal, mul_zero, sub_zero]
  have hcross : Integrable (fun p : Ω × Ω => K p.1 p.2 * L p.1 p.2) (μ.prod μ) :=
    hKlp.integrable_mul hLlp
  have hi12 : Integrable (fun p : Ω × Ω => (L p.1 p.2) ^ 2 -
      2 * a * (K p.1 p.2 * L p.1 p.2)) (μ.prod μ) :=
    hLlp.integrable_sq.sub (hcross.const_mul (2 * a))
  have hnorm : (∫ p : Ω × Ω, (L p.1 p.2 - a * K p.1 p.2) ^ 2 ∂μ.prod μ) =
      (∫ p : Ω × Ω, (L p.1 p.2) ^ 2 ∂μ.prod μ) -
        (∫ p : Ω × Ω, K p.1 p.2 * L p.1 p.2 ∂μ.prod μ) ^ 2 / Z := by
    calc
      _ = ∫ p : Ω × Ω, ((L p.1 p.2) ^ 2 - 2 * a * (K p.1 p.2 * L p.1 p.2)) +
          a ^ 2 * (K p.1 p.2) ^ 2 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by ring)
      _ = _ := by
        rw [integral_add hi12 (hKlp.integrable_sq.const_mul (a ^ 2)),
          integral_sub hLlp.integrable_sq (hcross.const_mul (2 * a)),
          integral_const_mul, integral_const_mul]
        dsimp only [a]
        have hZ : Z ≠ 0 := ne_of_gt hpositive
        field_simp
        ring
  have hcauchy := integral_mul_sq_le (fun p : Ω × Ω => J p.1 p.2)
    (fun p => L p.1 p.2 - a * K p.1 p.2) hJlp hRlp
  rw [hpair, hnorm] at hcauchy
  have hvariance := composed_moment_variance_le_half_square K hK B hB0 hKB hsym hpositive
  have hJ0 : 0 ≤ ∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hbound := hcauchy.trans (mul_le_mul_of_nonneg_left hvariance hJ0)
  dsimp only [L, Z] at hbound
  nlinarith

end Erdos1017.KernelOperator
