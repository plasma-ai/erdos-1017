module

public import Erdos1017.Exclusions.Common.KernelHilbertSchmidtSpectrum
public import Erdos1017.Models.Kernel.KernelLinearCombination
public import Erdos1017.Models.Kernel.KernelScalarPerturbation

/-!
# Spectral moments of composed kernels

The composition `composedKernel` of two bounded scalar kernels is defined and
shown to give exactly the composed quotient operators; the eigenbasis of the
kernel diagonalizes the square kernel, giving its fourth and signed cubic
moments, and the sharp spectral variance inequality holds between
composed-kernel moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators Classical

namespace Erdos1017.KernelOperator

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual integral composition of two bounded scalar kernels. -/
def composedKernel (K L : Ω → Ω → ℝ) (x y : Ω) : ℝ := ∫ z, K x z * L z y ∂μ

theorem measurable_composedKernel (K L : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L)) :
    Measurable (Function.uncurry (composedKernel (μ := μ) K L)) := by
  have hm : Measurable (fun p : (Ω × Ω) × Ω => K p.1.1 p.2 * L p.2 p.1.2) :=
    (hK.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hL.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem composedKernel_bound (K L : Ω → Ω → ℝ) (B C : ℝ) (hB0 : 0 ≤ B)
    (hK : ∀ x y, ‖K x y‖ ≤ B) (hL : ∀ x y, ‖L x y‖ ≤ C) (x y : Ω) :
    ‖composedKernel (μ := μ) K L x y‖ ≤ B * C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := B * C)
    (f := fun z => K x z * L z y)
    (Eventually.of_forall (fun z => by
    rw [norm_mul]
    exact mul_le_mul (hK x z) (hL z y) (norm_nonneg _) hB0))
  simpa only [composedKernel, probReal_univ, mul_one] using h

/-- Fubini identifies the genuine composed-kernel action with the
successive old integral actions. All inputs are integrable L² classes. -/
theorem apply_composedKernel (K L : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (B C : ℝ) (hB0 : 0 ≤ B)
    (hKB : ∀ x y, ‖K x y‖ ≤ B) (hLC : ∀ x y, ‖L x y‖ ≤ C)
    (f : Lp ℝ 2 μ) (x : Ω) :
    applyKernel (μ := μ) (composedKernel (μ := μ) K L) f x =
      applyKernel (μ := μ) K (applyKernel (μ := μ) L f) x := by
  have hf : Integrable (fun y => f y) μ := (Lp.memLp f).integrable (by norm_num)
  have hi : Integrable (fun p : Ω × Ω => K x p.1 * L p.1 p.2 * f p.2) (μ.prod μ) := by
    apply ((hf.norm.comp_snd μ).const_mul (B * C)).mono'
      (((hK.comp (measurable_const.prodMk measurable_fst)).aestronglyMeasurable.mul
        hL.aestronglyMeasurable).mul hf.aestronglyMeasurable.comp_snd)
    exact Eventually.of_forall (fun p => by
      change ‖K x p.1 * L p.1 p.2 * f p.2‖ ≤ B * C * ‖f p.2‖
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hKB x p.1) (hLC p.1 p.2) (norm_nonneg _) hB0) (norm_nonneg _))
  change (∫ y, (∫ z, K x z * L z y ∂μ) * f y ∂μ) = _
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap hi]
  change (∫ z, ∫ y, K x z * L z y * f y ∂μ ∂μ) =
    ∫ z, K x z * (∫ y, L z y * f y ∂μ) ∂μ
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    simp_rw [mul_assoc]
    rw [integral_const_mul])

/-- The actual composed kernel gives exactly the composed quotient
operators, not merely their formal eigenvalue products. -/
theorem operator_composedKernel (K L : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (B C : ℝ) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hKB : ∀ x y, ‖K x y‖ ≤ B) (hLC : ∀ x y, ‖L x y‖ ≤ C) :
    operator (composedKernel (μ := μ) K L) (mul_nonneg hB0 hC0)
        (measurable_composedKernel (μ := μ) K L hK hL).aestronglyMeasurable
        (Eventually.of_forall (fun p =>
          composedKernel_bound (μ := μ) K L B C hB0 hKB hLC p.1 p.2)) =
      (operator (μ := μ) K hB0 hK.aestronglyMeasurable
        (Eventually.of_forall (fun p => hKB p.1 p.2))).comp
        (operator (μ := μ) L hC0 hL.aestronglyMeasurable
          (Eventually.of_forall (fun p => hLC p.1 p.2))) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let T := operator (μ := μ) L hC0 hL.aestronglyMeasurable
    (Eventually.of_forall (fun p => hLC p.1 p.2))
  have he : applyKernel (μ := μ) K (T f) = applyKernel (μ := μ) K (applyKernel (μ := μ) L f) :=
    applyKernel_congr (onL2_coe L hL.aestronglyMeasurable
      (Eventually.of_forall (fun p => hLC p.1 p.2)) f)
  filter_upwards [onL2_coe (composedKernel (μ := μ) K L)
    (measurable_composedKernel (μ := μ) K L hK hL).aestronglyMeasurable
    (Eventually.of_forall (fun p =>
          composedKernel_bound (μ := μ) K L B C hB0 hKB hLC p.1 p.2)) f,
    onL2_coe K hK.aestronglyMeasurable (Eventually.of_forall (fun p => hKB p.1 p.2))
      (T f)] with x hx hy
  change onL2 (composedKernel (μ := μ) K L)
    (measurable_composedKernel (μ := μ) K L hK hL).aestronglyMeasurable
    (Eventually.of_forall (fun p =>
          composedKernel_bound (μ := μ) K L B C hB0 hKB hLC p.1 p.2)) f x =
    onL2 K hK.aestronglyMeasurable (Eventually.of_forall (fun p => hKB p.1 p.2)) (T f) x
  rw [hx, hy, he]
  exact apply_composedKernel K L hK hL B C hB0 hKB hLC f x

omit [IsProbabilityMeasure μ] in
/-- Pointwise symmetry of the original kernel gives pointwise symmetry
of its genuine square kernel. -/
theorem composedKernel_self_symm (K : Ω → Ω → ℝ)
    (hsym : ∀ x y, K x y = K y x) (x y : Ω) :
    composedKernel (μ := μ) K K x y = composedKernel (μ := μ) K K y x := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [hsym x z, hsym z y]
    ring)

/-- The same actual old eigenbasis diagonalizes the genuine square
kernel, giving its fourth moment without an absolute eigenvalue sum. -/
theorem hasSum_eigenvalues_fourth_composed [Countable ι]
    (K : Ω → Ω → ℝ) (hK : Measurable (Function.uncurry K))
    (B : ℝ) (hB0 : 0 ≤ B) (hKB : ∀ x y, ‖K x y‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK.aestronglyMeasurable
      (Eventually.of_forall (fun p => hKB p.1 p.2)) (b i) = t i • b i) :
    HasSum (fun i => (t i) ^ 4)
      (∫ p : Ω × Ω, (composedKernel (μ := μ) K K p.1 p.2) ^ 2 ∂μ.prod μ) := by
  let L := composedKernel (μ := μ) K K
  have hL := measurable_composedKernel (μ := μ) K K hK hK
  have hLB : ∀ᵐ p ∂μ.prod μ, ‖L p.1 p.2‖ ≤ B * B :=
    Eventually.of_forall (fun p => composedKernel_bound K K B B hB0 hKB hKB p.1 p.2)
  have hcomp := operator_composedKernel (μ := μ) K K hK hK B B hB0 hB0 hKB hKB
  have heigenL (i : ι) : operator L (mul_nonneg hB0 hB0) hL.aestronglyMeasurable hLB (b i) =
      (t i) ^ 2 • b i := by
    rw [hcomp, ContinuousLinearMap.comp_apply, heigen i, map_smul, heigen i, smul_smul]
    congr 1
    ring
  convert hasSum_eigenvalues_sq L (mul_nonneg hB0 hB0) hL.aestronglyMeasurable hLB b
    (fun i => (t i) ^ 2) heigenL using 1
  funext i
  ring

/-- Pointwise bounded kernel addition agrees with addition of the actual
quotient operators used by the square Parseval identity. -/
theorem operator_add_pointwise (K L : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (B C : ℝ) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hKB : ∀ x y, ‖K x y‖ ≤ B) (hLC : ∀ x y, ‖L x y‖ ≤ C) :
    operator (μ := μ) (fun x y => K x y + L x y) (add_nonneg hB0 hC0)
        (hK.add hL).aestronglyMeasurable
        (Eventually.of_forall (fun p => (norm_add_le _ _).trans
          (add_le_add (hKB p.1 p.2) (hLC p.1 p.2)))) =
      operator (μ := μ) K hB0 hK.aestronglyMeasurable
        (Eventually.of_forall (fun p => hKB p.1 p.2)) +
      operator (μ := μ) L hC0 hL.aestronglyMeasurable
        (Eventually.of_forall (fun p => hLC p.1 p.2)) := by
  simpa only [one_mul, norm_one, mul_one, one_smul] using
    operator_add_smul_kernel (μ := μ) L K hC0 hB0 hL.aestronglyMeasurable hK.aestronglyMeasurable
      (Eventually.of_forall (fun p => hLC p.1 p.2))
      (Eventually.of_forall (fun p => hKB p.1 p.2)) 1

/-- Polarizing the square Parseval identity for the genuine sum kernel
identifies the signed cubic spectral moment with its actual kernel integral. -/
theorem hasSum_eigenvalues_cube_composed [Countable ι]
    (K : Ω → Ω → ℝ) (hK : Measurable (Function.uncurry K))
    (B : ℝ) (hB0 : 0 ≤ B) (hKB : ∀ x y, ‖K x y‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK.aestronglyMeasurable
      (Eventually.of_forall (fun p => hKB p.1 p.2)) (b i) = t i • b i) :
    HasSum (fun i => (t i) ^ 3)
      (∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ) := by
  let L := composedKernel (μ := μ) K K
  have hL := measurable_composedKernel (μ := μ) K K hK hK
  have hLB : ∀ x y, ‖L x y‖ ≤ B * B :=
    composedKernel_bound (μ := μ) K K B B hB0 hKB hKB
  have hcomp := operator_composedKernel (μ := μ) K K hK hK B B hB0 hB0 hKB hKB
  have heigenL (i : ι) : operator L (mul_nonneg hB0 hB0) hL.aestronglyMeasurable
      (Eventually.of_forall (fun p => hLB p.1 p.2)) (b i) = (t i) ^ 2 • b i := by
    rw [hcomp, ContinuousLinearMap.comp_apply, heigen i, map_smul, heigen i, smul_smul]
    congr 1
    ring
  have h₂ := hasSum_eigenvalues_sq K hB0 hK.aestronglyMeasurable
    (Eventually.of_forall (fun p => hKB p.1 p.2)) b t heigen
  have h₄ := hasSum_eigenvalues_fourth_composed K hK B hB0 hKB b t heigen
  let T := operator (μ := μ) K hB0 hK.aestronglyMeasurable
    (Eventually.of_forall (fun p => hKB p.1 p.2))
  have ht (i : ι) : |t i| ≤ ‖T‖ := by
    have hi := T.le_opNorm (b i)
    rw [heigen i, norm_smul, b.orthonormal.norm_eq_one, mul_one, mul_one,
      Real.norm_eq_abs] at hi
    exact hi
  have h₃ := (SpectralSquareVariance.summable_cube_fourth t h₂.summable ‖T‖ ht).1
  have hadd := operator_add_pointwise (μ := μ) K L hK hL B (B * B) hB0
    (mul_nonneg hB0 hB0) hKB hLB
  have heigenAdd (i : ι) : operator (fun x y => K x y + L x y)
      (add_nonneg hB0 (mul_nonneg hB0 hB0)) (hK.add hL).aestronglyMeasurable
      (Eventually.of_forall (fun p => (norm_add_le _ _).trans
        (add_le_add (hKB p.1 p.2) (hLB p.1 p.2)))) (b i) =
        (t i + (t i) ^ 2) • b i := by
    rw [hadd, add_apply, heigen i, heigenL i, add_smul]
  have hplus := hasSum_eigenvalues_sq (fun x y => K x y + L x y)
    (add_nonneg hB0 (mul_nonneg hB0 hB0)) (hK.add hL).aestronglyMeasurable
    (Eventually.of_forall (fun p => (norm_add_le _ _).trans
      (add_le_add (hKB p.1 p.2) (hLB p.1 p.2)))) b
    (fun i => t i + (t i) ^ 2) heigenAdd
  have hpoly : HasSum (fun i => (t i + (t i) ^ 2) ^ 2)
      ((∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) + 2 * (∑' i, (t i) ^ 3) +
        ∫ p : Ω × Ω, (L p.1 p.2) ^ 2 ∂μ.prod μ) := by
    convert (h₂.add (h₃.hasSum.mul_left 2)).add h₄ using 1
    funext i
    ring
  have hKlp : MemLp (fun p : Ω × Ω => K p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hK.aestronglyMeasurable B
      (Eventually.of_forall (fun p => hKB p.1 p.2))
  have hLlp : MemLp (fun p : Ω × Ω => L p.1 p.2) 2 (μ.prod μ) :=
    MemLp.of_bound hL.aestronglyMeasurable (B * B)
      (Eventually.of_forall (fun p => hLB p.1 p.2))
  have hiKL : Integrable (fun p : Ω × Ω => K p.1 p.2 * L p.1 p.2) (μ.prod μ) :=
    hKlp.integrable_mul hLlp
  have hi12 : Integrable (fun p : Ω × Ω => (K p.1 p.2) ^ 2 +
      2 * (K p.1 p.2 * L p.1 p.2)) (μ.prod μ) :=
    hKlp.integrable_sq.add (hiKL.const_mul 2)
  have hexpand : (∫ p : Ω × Ω, (K p.1 p.2 + L p.1 p.2) ^ 2 ∂μ.prod μ) =
      (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) +
        2 * (∫ p : Ω × Ω, K p.1 p.2 * L p.1 p.2 ∂μ.prod μ) +
        ∫ p : Ω × Ω, (L p.1 p.2) ^ 2 ∂μ.prod μ := by
    calc
      _ = ∫ p : Ω × Ω, ((K p.1 p.2) ^ 2 + 2 * (K p.1 p.2 * L p.1 p.2)) +
          (L p.1 p.2) ^ 2 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by ring)
      _ = _ := by
        rw [integral_add hi12 hLlp.integrable_sq,
          integral_add hKlp.integrable_sq (hiKL.const_mul 2), integral_const_mul]
  have heq := hpoly.unique hplus
  have hcross : (∑' i, (t i) ^ 3) =
      ∫ p : Ω × Ω, K p.1 p.2 * L p.1 p.2 ∂μ.prod μ := by
    linarith
  rw [← hcross]
  exact h₃.hasSum

/-- The sharp spectral variance inequality is an inequality between actual
composed-kernel moments. The kernel constructs its own eigenbasis. -/
theorem composed_moment_variance_le_half_square
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) (hK : Measurable (Function.uncurry K))
    (B : ℝ) (hB0 : 0 ≤ B) (hKB : ∀ x y, ‖K x y‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) :
    (∫ p : Ω × Ω, (composedKernel (μ := μ) K K p.1 p.2) ^ 2 ∂μ.prod μ) -
        (∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ) ^ 2 /
          (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ^ 2 / 2 := by
  obtain ⟨κ, hc, b, t, heigen, _, _, _, hvariance⟩ := exists_countable_square_spectrum K
    hB0 hK.aestronglyMeasurable (Eventually.of_forall (fun p => hKB p.1 p.2)) hsym
  let : Countable κ := hc
  have h₃ := hasSum_eigenvalues_cube_composed K hK B hB0 hKB b t heigen
  have h₄ := hasSum_eigenvalues_fourth_composed K hK B hB0 hKB b t heigen
  simpa only [h₃.tsum_eq, h₄.tsum_eq] using hvariance hpositive

end Erdos1017.KernelOperator
