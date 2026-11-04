module

public import Erdos1017.Models.Kernel.KernelInjectivity
public import Erdos1017.Models.Kernel.SignedHilbertFeature

/-!
# Kernels represented by Hilbert features

A measurable signed Hilbert-feature kernel (`featureKernel`) acts as prescribed
on every spectral basis vector via a Bochner integral, and bounded measurable
spectral features recover the original kernel almost everywhere by equality of
integral operators.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Multiplying a bounded Hilbert feature by an L2 scalar is integrable. -/
theorem feature_smul_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Ω → E) (hF : AEStronglyMeasurable F μ) {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ R) (f : Lp ℝ 2 μ) :
    Integrable (fun x => f x • F x) μ := by
  have hfi := (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply (hfi.norm.const_mul R).mono' ((Lp.memLp f).aestronglyMeasurable.smul hF)
  filter_upwards [hR] with x hx
  change ‖f x • F x‖ ≤ R * ‖f x‖
  rw [norm_smul, mul_comm R]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- Integrating a feature against a basis vector recovers its single
spectral coordinate. -/
theorem feature_basis_integral [DecidableEq ι] (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (F : Ω → lp (fun _ : ι => ℝ) 2) (hF : AEStronglyMeasurable F μ) {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ R)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x) (j : ι) :
    (∫ x, b j x • F x ∂μ) = lp.single (E := fun _ : ι => ℝ) 2 j (Real.sqrt |t j|) := by
  classical
  have hi := feature_smul_integrable F hF hR (b j)
  apply lp.ext
  funext i
  change (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i) (∫ x, b j x • F x ∂μ) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  have heq : (∫ x, (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i) (b j x • F x) ∂μ) =
      Real.sqrt |t i| * ⟪b i, b j⟫ := by
    rw [L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcoord] with x hx
    change b j x * F x i = _
    rw [hx i, RCLike.inner_apply]
    simp only [conj_trivial]
    ring
  rw [heq, orthonormal_iff_ite.mp b.orthonormal]
  by_cases hij : i = j <;> simp [lp.single_apply, hij]

/-- The measurable signed Hilbert-feature kernel. -/
def featureKernel (t : ι → ℝ) (F : Ω → lp (fun _ : ι => ℝ) 2) (x y : Ω) : ℝ :=
  ⟪spectralSign t (F x), F y⟫

theorem featureKernel_measurable (t : ι → ℝ) (F : Ω → lp (fun _ : ι => ℝ) 2)
    (hF : AEStronglyMeasurable F μ) :
    AEStronglyMeasurable (fun z : Ω × Ω => featureKernel t F z.1 z.2) (μ.prod μ) :=
  ((spectralSign t).continuous.comp_aestronglyMeasurable hF.comp_fst).inner hF.comp_snd

theorem featureKernel_bound (t : ι → ℝ) (F : Ω → lp (fun _ : ι => ℝ) 2)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ R) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖featureKernel t F z.1 z.2‖ ≤ R ^ 2 := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hR,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hR] with z hx hy
  calc
    ‖featureKernel t F z.1 z.2‖ ≤ ‖spectralSign t (F z.1)‖ * ‖F z.2‖ := norm_inner_le_norm _ _
    _ = ‖F z.1‖ * ‖F z.2‖ := by rw [(spectralSign t).norm_map]
    _ ≤ R * R := mul_le_mul hx hy (norm_nonneg _) hR0
    _ = R ^ 2 := by ring

/-- The feature kernel has the prescribed action on every spectral basis
vector, obtained by an actual Bochner integral. -/
theorem apply_featureKernel_basis (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (F : Ω → lp (fun _ : ι => ℝ) 2) (hF : AEStronglyMeasurable F μ) {R : ℝ}
    (hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ R)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x) (j : ι) :
    ∀ᵐ x ∂μ, applyKernel (μ := μ) (featureKernel t F) (b j) x = t j * b j x := by
  classical
  have hi := feature_smul_integrable F hF hR (b j)
  filter_upwards [hcoord] with x hx
  calc
    applyKernel (μ := μ) (featureKernel t F) (b j) x =
        ∫ y, ⟪spectralSign t (F x), b j y • F y⟫ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp only [featureKernel, inner_smul_right]; ring)
    _ = ⟪spectralSign t (F x), ∫ y, b j y • F y ∂μ⟫ := integral_inner hi _
    _ = ⟪spectralSign t (F x), lp.single 2 j (Real.sqrt |t j|)⟫ := by
      rw [feature_basis_integral b t F hF hR hcoord j]
    _ = t j * b j x := by
      rw [lp.inner_single_right, RCLike.inner_apply]
      change Real.sqrt |t j| * (if t j < 0 then -F x j else F x j) = _
      rw [hx j, mul_comm]
      simpa only [mul_one] using signed_sqrt_mul (t j) (b j x) 1

/-- Bounded measurable spectral features recover the original kernel almost
everywhere, by equality of their actual integral operators. -/
theorem featureKernel_represents [Countable ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (F : Ω → lp (fun _ : ι => ℝ) 2) (hF : AEStronglyMeasurable F μ) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ R)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫ := by
  let L := featureKernel t F
  have hL := featureKernel_measurable t F hF
  have hLB := featureKernel_bound t F hR0 hR
  have hLeigen (j : ι) : operator L (sq_nonneg R) hL hLB (b j) = t j • b j := by
    apply Lp.ext
    filter_upwards [onL2_coe L hL hLB (b j), apply_featureKernel_basis b t F hF hR hcoord j,
      Lp.coeFn_smul (t j) (b j)] with x hx heq hs
    change onL2 L hL hLB (b j) x = _
    rw [hx, heq, hs]
    rfl
  have hops : operator K hB0 hK hB = operator L (sq_nonneg R) hL hLB := by
    apply operator_eq_of_hilbertBasis b
    intro i
    rw [heigen i, hLeigen i]
  have hzero : operator (μ := μ) (fun x y => K x y - L x y)
      (add_nonneg hB0 (sq_nonneg R)) (hK.sub hL) (kernel_sub_bound hB hLB) = 0 := by
    rw [operator_sub K L hB0 (sq_nonneg R) hK hL hB hLB, hops, sub_self]
  have hz := kernel_ae_zero_of_operator_eq_zero b (fun x y => K x y - L x y)
    (add_nonneg hB0 (sq_nonneg R)) (hK.sub hL) (kernel_sub_bound hB hLB) hzero
  exact hz.mono (fun z hz => sub_eq_zero.mp hz)

end Erdos1017.KernelOperator
