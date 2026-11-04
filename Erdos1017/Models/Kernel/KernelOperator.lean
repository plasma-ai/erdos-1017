module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Integral operators of bounded measurable kernels

The integral action of a real measurable kernel (`applyKernel`) is measurable,
controlled by the input L1 norm outside a row-null set, and defines a bounded
integral operator on L2 (`operator`) whose bilinear integral is integrable;
product-almost-everywhere symmetry of the kernel gives a symmetric operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The integral action of a real measurable kernel on a representative. -/
def applyKernel (K : Ω → Ω → ℝ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∫ y, K x y * f y ∂μ

/-- Bounded kernels act on integrable functions through an integrable joint
integrand. All bounds are modulo the product measure. -/
theorem integrable_joint {K : Ω → Ω → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun z : Ω × Ω => K z.1 z.2 * f z.2) (μ.prod μ) := by
  apply ((hf.norm.comp_snd μ).const_mul B).mono'
    (hK.mul hf.aestronglyMeasurable.comp_snd)
  filter_upwards [hB] with z hz
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hz (norm_nonneg (f z.2))

/-- The pointwise integral is measurable and uniformly controlled by the input
L1 norm outside a row-null set. -/
theorem applyKernel_bound {K : Ω → Ω → ℝ} {B : ℝ}
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ‖applyKernel (μ := μ) K f x‖ ≤ B * ∫ y, ‖f y‖ ∂μ := by
  filter_upwards [Measure.ae_ae_of_ae_prod hB] with x hx
  calc
    ‖applyKernel (μ := μ) K f x‖ ≤ ∫ y, B * ‖f y‖ ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul B)
      filter_upwards [hx] with y hy
      simpa only [norm_mul] using mul_le_mul_of_nonneg_right hy (norm_nonneg (f y))
    _ = B * ∫ y, ‖f y‖ ∂μ := integral_const_mul _ _

/-- A bounded measurable kernel maps every L2 representative to L2. -/
theorem applyKernel_memLp {K : Ω → Ω → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    MemLp (applyKernel (μ := μ) K f) 2 μ := by
  have hfi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  exact MemLp.of_bound (integrable_joint hK hB hfi).aestronglyMeasurable.integral_prod_right'
    (B * ∫ y, ‖f y‖ ∂μ) (applyKernel_bound hB hfi)

omit [IsProbabilityMeasure μ] in
/-- Changing the input on a null set does not change any row integral. -/
theorem applyKernel_congr {K : Ω → Ω → ℝ} {f g : Ω → ℝ}
    (hfg : f =ᵐ[μ] g) : applyKernel (μ := μ) K f = applyKernel (μ := μ) K g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- The integral L1 norm is bounded by the L2 norm on a probability space. -/
theorem integral_norm_le_L2 (f : Lp ℝ 2 μ) : (∫ x, ‖f x‖ ∂μ) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable]
  change (eLpNorm (⇑f) 1 μ).toReal ≤ (eLpNorm (⇑f) 2 μ).toReal
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

/-- The kernel action descends to the quotient by almost-everywhere equality. -/
def onL2 (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (applyKernel_memLp hK hB (Lp.memLp f)).toLp (applyKernel (μ := μ) K f)

theorem onL2_coe (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f : Lp ℝ 2 μ) :
    ⇑(onL2 K hK hB f) =ᵐ[μ] applyKernel (μ := μ) K f := MemLp.coeFn_toLp _

theorem onL2_norm_le (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f : Lp ℝ 2 μ) :
    ‖onL2 K hK hB f‖ ≤ B * ‖f‖ := by
  have hpoint : ∀ᵐ x ∂μ, ‖onL2 K hK hB f x‖ ≤ B * ‖f‖ := by
    filter_upwards [onL2_coe K hK hB f,
      applyKernel_bound hB ((Lp.memLp f).integrable (by norm_num))] with x hx hb
    rw [hx]
    exact hb.trans (mul_le_mul_of_nonneg_left (integral_norm_le_L2 f) hB0)
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (mul_nonneg hB0 (norm_nonneg f)) hpoint

theorem onL2_add (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f g : Lp ℝ 2 μ) :
    onL2 K hK hB (f + g) = onL2 K hK hB f + onL2 K hK hB g := by
  apply Lp.ext
  have hf := integrable_joint hK hB ((Lp.memLp f).integrable (by norm_num))
  have hg := integrable_joint hK hB ((Lp.memLp g).integrable (by norm_num))
  filter_upwards [onL2_coe K hK hB (f + g), onL2_coe K hK hB f,
    onL2_coe K hK hB g, Lp.coeFn_add (onL2 K hK hB f) (onL2 K hK hB g),
    hf.prod_right_ae, hg.prod_right_ae] with x hsum hfx hgx hadd hfi hgi
  rw [hsum, hadd, Pi.add_apply, hfx, hgx, applyKernel_congr (Lp.coeFn_add f g)]
  simp only [applyKernel, Pi.add_apply, mul_add]
  exact integral_add hfi hgi

theorem onL2_smul (K : Ω → Ω → ℝ) {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (c : ℝ) (f : Lp ℝ 2 μ) :
    onL2 K hK hB (c • f) = c • onL2 K hK hB f := by
  apply Lp.ext
  filter_upwards [onL2_coe K hK hB (c • f), onL2_coe K hK hB f,
    Lp.coeFn_smul c (onL2 K hK hB f)] with x hcf hf hsmul
  rw [hcf, hsmul, Pi.smul_apply, hf, applyKernel_congr (Lp.coeFn_smul c f)]
  simp only [applyKernel, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (K x _) c]
  rw [show (fun y => c * K x y * f y) = (fun y => c * (K x y * f y)) by
    funext y; ring, integral_const_mul]

/-- The bounded integral operator defined by a product-measurable kernel. -/
def operator (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := onL2 K hK hB
      map_add' := onL2_add K hK hB
      map_smul' := onL2_smul K hK hB }
    B (onL2_norm_le K hB0 hK hB)

/-- The bilinear integral is integrable even though the L2 representatives
need not be bounded. -/
theorem integrable_bilinear {K : Ω → Ω → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f g : Lp ℝ 2 μ) :
    Integrable (fun z : Ω × Ω => K z.1 z.2 * f z.2 * g z.1) (μ.prod μ) := by
  have hf := (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg := (Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ((hg.norm.mul_prod hf.norm).const_mul B).mono'
    ((hK.mul hf.aestronglyMeasurable.comp_snd).mul hg.aestronglyMeasurable.comp_fst)
  filter_upwards [hB] with z hz
  simp only [Pi.mul_apply, norm_mul]
  calc
    ‖K z.1 z.2‖ * ‖f z.2‖ * ‖g z.1‖ ≤ B * ‖f z.2‖ * ‖g z.1‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) (norm_nonneg _)
    _ = B * (‖g z.1‖ * ‖f z.2‖) := by ring

theorem operator_inner (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B) (f g : Lp ℝ 2 μ) :
    ⟪operator K hB0 hK hB f, g⟫ =
      ∫ z : Ω × Ω, K z.1 z.2 * f z.2 * g z.1 ∂μ.prod μ := by
  rw [L2.inner_def, integral_prod _ (integrable_bilinear hK hB f g)]
  apply integral_congr_ae
  filter_upwards [onL2_coe K hK hB f] with x hx
  change inner ℝ (onL2 K hK hB f x) (g x) = _
  rw [hx, RCLike.inner_apply]
  simp only [conj_trivial, applyKernel, integral_mul_const]
  ring

/-- Product-almost-everywhere symmetry of the kernel gives a symmetric L2
operator; no pointwise choice of its diagonal is required. -/
theorem operator_symmetric (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = K z.2 z.1) :
    (operator K hB0 hK hB).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪operator K hB0 hK hB f, g⟫ = ⟪f, operator K hB0 hK hB g⟫
  rw [← real_inner_comm f (operator K hB0 hK hB g), operator_inner K hB0 hK hB f g,
    operator_inner K hB0 hK hB g f,
    ← integral_prod_swap (fun z : Ω × Ω => K z.1 z.2 * g z.2 * f z.1)]
  apply integral_congr_ae
  filter_upwards [hsym] with z hz
  change K z.1 z.2 * f z.2 * g z.1 = K z.2 z.1 * g z.1 * f z.2
  rw [hz]
  ring

end Erdos1017.KernelOperator
