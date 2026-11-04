module

public import Erdos1017.Exclusions.Common.KernelOrthogonalCubic

/-!
# Cubic pairing from integrated copy rows

A bounded triangle integral can be regrouped at its other edge by Fubini,
integrating a copied-row bound produces the cubic pairing of the bounded
positive body with the missing-edge kernel, and with the orthogonal cubic
estimate this forces the universal-atom trace inequality for nonzero positive
body.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded triangle integral can be regrouped at its other old edge.
This is an actual Fubini identity, independent of a trace representation. -/
theorem integral_mul_composed_swap (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hKB : ∀ x y, ‖K x y‖ ≤ 1) (hJB : ∀ x y, ‖J x y‖ ≤ 1)
    (hsym : ∀ x y, K x y = K y x) :
    (∫ p : Ω × Ω, K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2 ∂μ.prod μ) =
      ∫ p : Ω × Ω, J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2 ∂μ.prod μ := by
  have hJK := measurable_composedKernel (μ := μ) J K hJ hK
  have hKK := measurable_composedKernel (μ := μ) K K hK hK
  have hi₁ : Integrable (fun p : Ω × Ω =>
      K p.1 p.2 * composedKernel (μ := μ) J K p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (hK.mul hJK).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hKB p.1 p.2)
          (composedKernel_bound (μ := μ) J K 1 1 (by norm_num) hJB hKB p.1 p.2)
          (norm_nonneg _) zero_le_one))
  have hi₂ : Integrable (fun p : Ω × Ω =>
      J p.1 p.2 * composedKernel (μ := μ) K K p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (hJ.mul hKK).aestronglyMeasurable 1
      (Eventually.of_forall (fun p => by
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul (hJB p.1 p.2)
          (composedKernel_bound (μ := μ) K K 1 1 (by norm_num) hKB hKB p.1 p.2)
          (norm_nonneg _) zero_le_one))
  rw [integral_prod _ hi₁, integral_prod _ hi₂]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    have hi : Integrable (fun p : Ω × Ω => K x p.1 * J x p.2 * K p.2 p.1) (μ.prod μ) :=
      Integrable.of_bound
        (((hK.comp (measurable_const.prodMk measurable_fst)).mul
          (hJ.comp (measurable_const.prodMk measurable_snd))).mul
          (hK.comp measurable_swap)).aestronglyMeasurable 1
        (Eventually.of_forall (fun p => by
          rw [norm_mul, norm_mul]
          calc
            _ ≤ (1 : ℝ) * 1 * 1 := mul_le_mul
              (mul_le_mul (hKB x p.1) (hJB x p.2) (norm_nonneg _) zero_le_one)
              (hKB p.2 p.1) (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num))
    change (∫ y, K x y * (∫ z, J x z * K z y ∂μ) ∂μ) =
      ∫ z, J x z * (∫ y, K x y * K y z ∂μ) ∂μ
    simp_rw [← integral_const_mul]
    have he : (∫ y, ∫ z, K x y * (J x z * K z y) ∂μ ∂μ) =
        ∫ z, ∫ y, K x y * J x z * K z y ∂μ ∂μ := by
      have he := integral_integral_swap (f := fun y z => K x y * J x z * K z y) hi
      simpa only [mul_assoc] using he
    rw [he]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        dsimp only
        rw [hsym z y]
        ring)))

/-- Integration of an actual copied-row bound produces the cubic pairing
of the original bounded positive body with the missing-edge kernel. -/
theorem integrated_copy_row_bound (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hsym : ∀ x y, K x y = K y x)
    (a g : ℝ) (hg : 0 ≤ g)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1)) :
    (a + g) * (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ≤
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
  have hsq : (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ≤
      ∫ p : Ω × Ω, K p.1 p.2 ∂μ.prod μ :=
    integral_mono_ae hKl.integrable_sq (hKl.integrable (by norm_num))
      (Eventually.of_forall (fun p => by nlinarith [(hK01 p.1 p.2).1, (hK01 p.1 p.2).2]))
  nlinarith [mul_le_mul_of_nonneg_left hsq hg]

/-- The genuine integrated copy bound and sharp orthogonal cubic estimate
force the universal-atom trace inequality whenever the positive body is nonzero. -/
theorem copy_row_trace_bound [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K J : Ω → Ω → ℝ)
    (hK : Measurable (Function.uncurry K)) (hJ : Measurable (Function.uncurry J))
    (hK01 : ∀ x y, K x y ∈ Set.Icc (0 : ℝ) 1)
    (hJB : ∀ x y, ‖J x y‖ ≤ 1) (hsym : ∀ x y, K x y = K y x)
    (a g : ℝ) (hg : 0 ≤ g) (hag : 0 ≤ a + g)
    (hpositive : 0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    (horthogonal : (∫ p : Ω × Ω, J p.1 p.2 * K p.1 p.2 ∂μ.prod μ) = 0)
    (hrow : ∀ᵐ p ∂μ.prod μ, a * (K p.1 p.2) ^ 2 + g * K p.1 p.2 ≤
      K p.1 p.2 * (composedKernel (μ := μ) J K p.1 p.2 +
        composedKernel (μ := μ) J K p.2 p.1)) :
    (a + g) ^ 2 ≤ 2 * (∫ p : Ω × Ω, (J p.1 p.2) ^ 2 ∂μ.prod μ) := by
  have hKB : ∀ x y, ‖K x y‖ ≤ 1 := fun x y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hK01 x y).1]
    exact (hK01 x y).2
  have hcopy := integrated_copy_row_bound K J hK hJ hK01 hJB hsym a g hg hrow
  have hsharp := orthogonal_composed_pairing_sq_le K J hK hJ 1 1 zero_le_one hKB hJB
    (Eventually.of_forall (fun p => hsym p.1 p.2)) hpositive horthogonal
  have hleft : 0 ≤ (a + g) * (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) :=
    mul_nonneg hag hpositive.le
  have hsquare := (sq_le_sq₀ hleft (hleft.trans hcopy)).mpr hcopy
  by_contra h
  have hdiff := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (sq_pos_of_pos hpositive)
  nlinarith

end Erdos1017.KernelOperator
