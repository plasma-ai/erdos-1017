module

public import Erdos1017.Models.Kernel.CompactEigenbasis

/-!
# Finite spectral parts of kernels

The finite spectral kernel (`finiteSpectralKernel`) is measurable and uniformly
bounded, its operator is the finite spectral sum of rank-one operators, and a
finite positive spectral part leaves a bounded measurable remainder kernel with
nonnegative integral quadratic form.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The actual finite spectral kernel formed from L2 representatives. -/
def finiteSpectralKernel (b : ι → Lp ℝ 2 μ) (t : ι → ℝ) (s : Finset ι)
    (x y : Ω) : ℝ := ∑ i ∈ s, t i * b i x * b i y

theorem finiteSpectralKernel_measurable (b : ι → Lp ℝ 2 μ) (t : ι → ℝ) (s : Finset ι) :
    AEStronglyMeasurable (fun z : Ω × Ω => finiteSpectralKernel (μ := μ) b t s z.1 z.2) (μ.prod μ) := by
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  exact ((Lp.memLp (b i)).aestronglyMeasurable.comp_fst.const_mul (t i)).mul
    (Lp.memLp (b i)).aestronglyMeasurable.comp_snd

omit [IsProbabilityMeasure μ] in
theorem apply_finiteSpectralKernel (b : ι → Lp ℝ 2 μ) (t : ι → ℝ) (s : Finset ι)
    (f : Lp ℝ 2 μ) (x : Ω) :
    applyKernel (μ := μ) (finiteSpectralKernel (μ := μ) b t s) f x =
      ∑ i ∈ s, t i * ⟪b i, f⟫ * b i x := by
  simp only [applyKernel, finiteSpectralKernel, Finset.sum_mul]
  have hi (i : ι) : Integrable (fun y => t i * b i x * b i y * f y) μ := by
    simpa only [Pi.mul_apply, mul_assoc] using
      ((Lp.memLp (b i)).integrable_mul (Lp.memLp f)).const_mul (t i * b i x)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : (∫ y, b i y * f y ∂μ) = ⟪b i, f⟫ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by simp [RCLike.inner_apply, mul_comm])
  calc
    (∫ y, t i * b i x * b i y * f y ∂μ) =
        (t i * b i x) * ∫ y, b i y * f y ∂μ := by
      simp_rw [mul_assoc]
      rw [integral_const_mul, integral_const_mul]
    _ = t i * ⟪b i, f⟫ * b i x := by rw [hinner]; ring

/-- The bounded kernel construction agrees exactly with the finite spectral
sum of rank-one operators. -/
theorem operator_finiteSpectralKernel (b : ι → Lp ℝ 2 μ) (t : ι → ℝ) (s : Finset ι)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => finiteSpectralKernel (μ := μ) b t s z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ B) :
    operator (Ω := Ω) (μ := μ) (B := B) (finiteSpectralKernel (μ := μ) b t s) hB0 hK hB =
      finiteSpectralOperator (E := Lp ℝ 2 μ) (ι := ι) b t s := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum s (fun i => (t i * ⟪b i, f⟫) • b i)
  have hsmul : ∀ᵐ x ∂μ, ∀ i ∈ s,
      ((t i * ⟪b i, f⟫) • b i) x = (t i * ⟪b i, f⟫) * b i x := by
    exact (s.eventually_all.mpr (fun i _ => Lp.coeFn_smul (t i * ⟪b i, f⟫) (b i)))
  filter_upwards [onL2_coe (finiteSpectralKernel (μ := μ) b t s)
    hK hB f, hsum, hsmul] with x hx hsumx hsmulx
  change onL2 (finiteSpectralKernel (μ := μ) b t s) hK hB f x = _
  rw [hx, apply_finiteSpectralKernel]
  have heq : finiteSpectralOperator b t s f = ∑ i ∈ s, (t i * ⟪b i, f⟫) • b i := by
    simp [finiteSpectralOperator, InnerProductSpace.rankOne_apply, smul_smul]
  rw [heq, hsumx]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hsmulx i hi).symm

/-- Essential bounds for the finitely many representatives give an actual
uniform bound for their finite spectral kernel. -/
theorem finiteSpectralKernel_bound (b : ι → Lp ℝ 2 μ) (t : ι → ℝ) (s : Finset ι)
    (a : ι → ℝ) (hb : ∀ i ∈ s, ∀ᵐ x ∂μ, ‖b i x‖ ≤ a i) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤
      ∑ i ∈ s, ‖t i‖ * (a i) ^ 2 := by
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s, ‖b i x‖ ≤ a i := s.eventually_all.mpr hb
  have hx := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hall
  have hy := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hall
  filter_upwards [hx, hy] with z hx hy
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hnonneg : 0 ≤ a i := (norm_nonneg _).trans (hx i hi)
  simp only [norm_mul]
  calc
    ‖t i‖ * ‖b i z.1‖ * ‖b i z.2‖ = ‖t i‖ * (‖b i z.1‖ * ‖b i z.2‖) := mul_assoc _ _ _
    _ ≤ ‖t i‖ * (a i * a i) := mul_le_mul_of_nonneg_left
      (mul_le_mul (hx i hi) (hy i hi) (norm_nonneg _) hnonneg) (norm_nonneg _)
    _ = ‖t i‖ * (a i) ^ 2 := by ring

omit [IsProbabilityMeasure μ] in
theorem kernel_sub_bound {K L : Ω → Ω → ℝ} {B C : ℝ}
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖L z.1 z.2‖ ≤ C) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2 - L z.1 z.2‖ ≤ B + C := by
  filter_upwards [hB, hC] with z hb hc
  exact (norm_sub_le _ _).trans (add_le_add hb hc)

/-- Subtracting bounded kernels subtracts their actual integral operators. -/
theorem operator_sub (K L : Ω → Ω → ℝ) {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hL : AEStronglyMeasurable (fun z : Ω × Ω => L z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖L z.1 z.2‖ ≤ C) :
    operator (μ := μ) (fun x y => K x y - L x y) (add_nonneg hB0 hC0)
      (hK.sub hL) (kernel_sub_bound hB hC) =
      operator K hB0 hK hB - operator L hC0 hL hC := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [sub_apply, inner_sub_left, operator_inner, operator_inner, operator_inner]
  simp_rw [sub_mul]
  exact integral_sub (integrable_bilinear hK hB f g) (integrable_bilinear hL hC f g)

/-- A finite positive spectral part leaves an actual bounded measurable
kernel whose integral quadratic form is nonnegative. -/
theorem negative_spectral_kernel_bounded_psd
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s : Finset ι) (hpos : ∀ i ∈ s, 0 < t i) (houtside : ∀ i ∉ s, t i ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
        (fun z : Ω × Ω => finiteSpectralKernel (μ := μ) b t s z.1 z.2 - K z.1 z.2) (μ.prod μ) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ,
        ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2 - K z.1 z.2‖ ≤ C) ∧
      ∀ f : Lp ℝ 2 μ,
        0 ≤ ∫ z : Ω × Ω,
          (finiteSpectralKernel (μ := μ) b t s z.1 z.2 - K z.1 z.2) * f z.2 * f z.1 ∂μ.prod μ := by
  let D := ∑ i ∈ s, ‖t i‖ * (B / t i) ^ 2
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  have hb (i : ι) (hi : i ∈ s) : ∀ᵐ x ∂μ, ‖b i x‖ ≤ B / t i := by
    simpa [b.orthonormal.norm_eq_one i, Real.norm_of_nonneg (hpos i hi).le] using
      eigenfunction_bound K hB0 hK hB (b i) (t i) (hpos i hi).ne' (heigen i)
  have hP := finiteSpectralKernel_measurable (μ := μ) b t s
  have hDP : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ D :=
    finiteSpectralKernel_bound b t s (fun i => B / t i) hb
  refine ⟨D + B, add_nonneg hD0 hB0, hP.sub hK, kernel_sub_bound hDP hB, ?_⟩
  intro f
  rw [← operator_inner (fun x y => finiteSpectralKernel (μ := μ) b t s x y - K x y)
    (add_nonneg hD0 hB0) (hP.sub hK) (kernel_sub_bound hDP hB),
    operator_sub _ _ hD0 hB0 hP hK hDP hB,
    operator_finiteSpectralKernel b t s hD0 hP hDP]
  exact finiteSpectralOperator_sub_nonneg b (operator K hB0 hK hB)
    (operator_symmetric K hB0 hK hB hsym) t heigen s houtside f

/-- A cell-indicator quadratic form is exactly the kernel integral over the
cell square, including null cells. -/
theorem indicator_quadratic_eq (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (s : Set Ω) (hs : MeasurableSet s) :
    ⟪operator K hB0 hK hB (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)),
      indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)⟫ =
      ∫ z in s ×ˢ s, K z.1 z.2 ∂μ.prod μ := by
  rw [operator_inner, ← integral_indicator (hs.prod hs)]
  have hf : ⇑(indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)) =ᵐ[μ]
      s.indicator (fun _ => 1) := indicatorConstLp_coeFn
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hf,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hf] with z hfst hsnd
  simp only [Function.comp_apply] at hfst hsnd
  rw [hfst, hsnd]
  by_cases hx : z.1 ∈ s <;> by_cases hy : z.2 ∈ s <;> simp [hx, hy]

end Erdos1017.KernelOperator
