module

public import Erdos1017.Models.Kernel.KernelSpectrum
public import Graphon.CutDistance
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Basic.Real.Pointwise

/-!
# Cut norm and the cubic operator estimate

The signed difference of two graphon representatives (`graphonDifference`)
defines a bounded L² operator whose norm cubed is controlled by the cut norm,
and the rectangle cut norm (`kernelCutNorm`) gives the same cubic estimate for
any bounded symmetric measurable kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The actual signed difference of two graphon representatives. -/
def graphonDifference (U W : Graphon Ω μ) (x y : Ω) : ℝ :=
  U.toAEEqFun (x, y) - W.toAEEqFun (x, y)

omit [IsProbabilityMeasure μ] in
theorem graphonDifference_measurable (U W : Graphon Ω μ) :
    AEStronglyMeasurable
      (fun z : Ω × Ω => graphonDifference U W z.1 z.2) (μ.prod μ) :=
  U.toAEEqFun.aestronglyMeasurable.sub W.toAEEqFun.aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
theorem graphonDifference_bound (U W : Graphon Ω μ) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖graphonDifference U W z.1 z.2‖ ≤ 1 := by
  filter_upwards [U.ae_mem_Icc, W.ae_mem_Icc] with z hu hw
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> dsimp [graphonDifference] <;> linarith [hu.1, hu.2, hw.1, hw.2]

omit [IsProbabilityMeasure μ] in
theorem graphonDifference_symmetric (U W : Graphon Ω μ) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      graphonDifference U W z.1 z.2 = graphonDifference U W z.2 z.1 := by
  filter_upwards [U.symm_ae, W.symm_ae] with z hu hw
  exact congrArg₂ (· - ·) hu.symm hw.symm

private theorem weighted_integrable (U W : Graphon Ω μ) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfbound : ∀ x, |f x| ≤ 1) (hgbound : ∀ x, |g x| ≤ 1) :
    Integrable (fun z : Ω × Ω => f z.1 * g z.2 * graphonDifference U W z.1 z.2)
      (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((hf.comp measurable_fst).aestronglyMeasurable.mul
      (hg.comp measurable_snd).aestronglyMeasurable |>.mul
        (graphonDifference_measurable U W))
  filter_upwards [graphonDifference_bound U W] with z hz
  change ‖f z.1 * g z.2 * graphonDifference U W z.1 z.2‖ ≤ 1
  simp only [norm_mul, Real.norm_eq_abs] at hz ⊢
  calc
    |f z.1| * |g z.2| * |graphonDifference U W z.1 z.2| ≤ (1 * 1) * 1 :=
      mul_le_mul (mul_le_mul (hfbound z.1) (hgbound z.2)
        (abs_nonneg _) (by norm_num)) hz (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem positive_weighted_le (U W : Graphon Ω μ) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfbound : ∀ x, f x ∈ Set.Icc 0 1) (hgbound : ∀ x, g x ∈ Set.Icc 0 1) :
    |∫ z : Ω × Ω, f z.1 * g z.2 * graphonDifference U W z.1 z.2 ∂μ.prod μ| ≤
      Graphon.cutNormDiff U W := by
  rw [integral_prod _ (weighted_integrable U W f g hf hg
    (fun x => by rw [abs_of_nonneg (hfbound x).1]; exact (hfbound x).2)
    (fun x => by rw [abs_of_nonneg (hgbound x).1]; exact (hgbound x).2))]
  exact Graphon.abs_weighted_integral_diff_le U W f g hf hg hfbound hgbound

/-- Rectangle cut norm controls signed measurable weights in the unit ball.
The factor four comes from their positive and negative parts. -/
theorem abs_signed_weighted_graphonDifference_le (U W : Graphon Ω μ) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfbound : ∀ x, |f x| ≤ 1) (hgbound : ∀ x, |g x| ≤ 1) :
    |∫ z : Ω × Ω, f z.1 * g z.2 * graphonDifference U W z.1 z.2 ∂μ.prod μ| ≤
      4 * Graphon.cutNormDiff U W := by
  let fp := fun x => max (f x) 0
  let fn := fun x => max (-f x) 0
  let gp := fun x => max (g x) 0
  let gn := fun x => max (-g x) 0
  have hfp : Measurable fp := hf.max measurable_const
  have hfn : Measurable fn := hf.neg.max measurable_const
  have hgp : Measurable gp := hg.max measurable_const
  have hgn : Measurable gn := hg.neg.max measurable_const
  have hfpb (x) : fp x ∈ Set.Icc 0 1 :=
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hfbound x)) (by norm_num)⟩
  have hfnb (x) : fn x ∈ Set.Icc 0 1 :=
    ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hfbound x)) (by norm_num)⟩
  have hgpb (x) : gp x ∈ Set.Icc 0 1 :=
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hgbound x)) (by norm_num)⟩
  have hgnb (x) : gn x ∈ Set.Icc 0 1 :=
    ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hgbound x)) (by norm_num)⟩
  let J := fun a b : Ω → ℝ =>
    ∫ z : Ω × Ω, a z.1 * b z.2 * graphonDifference U W z.1 z.2 ∂μ.prod μ
  have hi a b (ha : Measurable a) (hb : Measurable b)
      (hab : ∀ x, a x ∈ Set.Icc 0 1) (hbb : ∀ x, b x ∈ Set.Icc 0 1) :=
    weighted_integrable U W a b ha hb
      (fun x => by rw [abs_of_nonneg (hab x).1]; exact (hab x).2)
      (fun x => by rw [abs_of_nonneg (hbb x).1]; exact (hbb x).2)
  have heq : J f g = (J fp gp - J fp gn) - (J fn gp - J fn gn) := by
    have hf' (x) : f x = fp x - fn x := by
      dsimp [fp, fn]
      simp only [max_def]
      split_ifs <;> linarith
    have hg' (x) : g x = gp x - gn x := by
      dsimp [gp, gn]
      simp only [max_def]
      split_ifs <;> linarith
    have heq : (fun z : Ω × Ω => f z.1 * g z.2 * graphonDifference U W z.1 z.2) =
        (fun z => (fp z.1 * gp z.2 * graphonDifference U W z.1 z.2 -
          fp z.1 * gn z.2 * graphonDifference U W z.1 z.2) -
          (fn z.1 * gp z.2 * graphonDifference U W z.1 z.2 -
          fn z.1 * gn z.2 * graphonDifference U W z.1 z.2)) := by
      funext z
      rw [hf' z.1, hg' z.2]
      ring
    dsimp only [J]
    rw [heq]
    simpa only [Pi.sub_apply] using
      (integral_sub
        ((hi fp gp hfp hgp hfpb hgpb).sub (hi fp gn hfp hgn hfpb hgnb))
        ((hi fn gp hfn hgp hfnb hgpb).sub (hi fn gn hfn hgn hfnb hgnb))).trans
        (congrArg₂ (· - ·)
          (integral_sub (hi fp gp hfp hgp hfpb hgpb) (hi fp gn hfp hgn hfpb hgnb))
          (integral_sub (hi fn gp hfn hgp hfnb hgpb) (hi fn gn hfn hgn hfnb hgnb)))
  change |J f g| ≤ _
  rw [heq]
  have h1 := positive_weighted_le U W fp gp hfp hgp hfpb hgpb
  have h2 := positive_weighted_le U W fp gn hfp hgn hfpb hgnb
  have h3 := positive_weighted_le U W fn gp hfn hgp hfnb hgpb
  have h4 := positive_weighted_le U W fn gn hfn hgn hfnb hgnb
  exact (abs_sub _ _).trans ((add_le_add (abs_sub _ _) (abs_sub _ _)).trans (by
    change |J fp gp| + |J fp gn| + (|J fn gp| + |J fn gn|) ≤ _
    linarith))

/-- The bounded L² operator of the actual signed graphon difference. -/
def graphonDifferenceOperator (U W : Graphon Ω μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  operator (graphonDifference U W) (by norm_num)
    (graphonDifference_measurable U W) (graphonDifference_bound U W)

/-- The cubic cut estimate for every nonzero normalized eigenfunction.
No eigenfunction bound is assumed: it follows from the integral equation. -/
theorem graphonDifference_eigenvalue_cube_le (U W : Graphon Ω μ)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : t ≠ 0) (hnorm : ‖f‖ = 1)
    (heigen : graphonDifferenceOperator U W f = t • f) :
    |t| ^ 3 ≤ 4 * Graphon.cutNormDiff U W := by
  let u := fun x => max (-1 : ℝ) (min 1 (|t| * f x))
  have hum : Measurable u := measurable_const.max
    (measurable_const.min ((Lp.stronglyMeasurable f).measurable.const_mul |t|))
  have hub (x) : |u x| ≤ 1 := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hueq : ∀ᵐ x ∂μ, u x = |t| * f x := by
    have hb := eigenfunction_bound (graphonDifference U W) (by norm_num)
      (graphonDifference_measurable U W) (graphonDifference_bound U W)
      f t ht heigen
    filter_upwards [hb] with x hx
    have hx' : |t| * |f x| ≤ 1 := by
      have := (le_div_iff₀ (norm_pos_iff.mpr ht)).mp hx
      simpa [hnorm, Real.norm_eq_abs, mul_comm] using this
    have hval : abs (|t| * f x) ≤ 1 := by
      simpa only [abs_mul, abs_abs] using hx'
    dsimp [u]
    rw [min_eq_right (abs_le.mp hval).2, max_eq_right (abs_le.mp hval).1]
  have hinner : ⟪graphonDifferenceOperator U W f, f⟫ = t := by
    rw [heigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    ring
  have heq : (∫ z : Ω × Ω, u z.1 * u z.2 * graphonDifference U W z.1 z.2 ∂μ.prod μ) =
      |t| ^ 2 * t := by
    calc
      _ = ∫ z : Ω × Ω, |t| ^ 2 *
          (graphonDifference U W z.1 z.2 * f z.2 * f z.1) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae hueq,
          Measure.quasiMeasurePreserving_snd.ae hueq] with z hx hy
        rw [hx, hy]
        ring
      _ = |t| ^ 2 * t := by
        rw [integral_const_mul, ← operator_inner (graphonDifference U W) (by norm_num)
          (graphonDifference_measurable U W) (graphonDifference_bound U W)]
        exact congrArg (|t| ^ 2 * ·) hinner
  have h := abs_signed_weighted_graphonDifference_le U W u u hum hum hub hub
  rw [heq] at h
  convert h using 1
  rw [abs_mul, abs_pow, abs_abs]
  ring

/-- Cut convergence controls the full operator norm, rather than only
previously chosen eigenvalues. Compactness supplies a norm attaining
eigenvalue of one of the two signs. -/
theorem graphonDifferenceOperator_norm_cube_le
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] (U W : Graphon Ω μ) :
    ‖graphonDifferenceOperator U W‖ ^ 3 ≤ 4 * Graphon.cutNormDiff U W := by
  let T := graphonDifferenceOperator U W
  have hs : T.IsSymmetric := operator_symmetric (graphonDifference U W) (by norm_num)
    (graphonDifference_measurable U W) (graphonDifference_bound U W)
    (graphonDifference_symmetric U W)
  have hc : IsCompactOperator T := operator_isCompact (graphonDifference U W) (by norm_num)
    (graphonDifference_measurable U W) (graphonDifference_bound U W)
  by_cases hT : ‖T‖ = 0
  · change ‖T‖ ^ 3 ≤ _
    rw [hT]
    simpa only [zero_pow (show (3 : ℕ) ≠ 0 by decide)] using
      mul_nonneg (show 0 ≤ (4 : ℝ) by norm_num) (Graphon.cutNormDiff_nonneg U W)
  have : Nontrivial (Lp ℝ 2 μ) := by
    by_contra h
    have : Subsingleton (Lp ℝ 2 μ) := not_nontrivial_iff_subsingleton.mp h
    exact hT (by simp)
  have hspec : ‖T‖ ∈ spectrum ℝ T ∨ -‖T‖ ∈ spectrum ℝ T := by
    by_contra! h
    have h1 : algebraMap ℝ ℝ ‖T‖ ∈ resolventSet ℝ T := by
      simpa only [spectrum, Set.mem_compl_iff, not_not,
        Algebra.algebraMap_self, RingHom.id_apply] using h.1
    have h2 : -algebraMap ℝ ℝ ‖T‖ ∈ resolventSet ℝ T := by
      simpa only [spectrum, Set.mem_compl_iff, not_not,
        Algebra.algebraMap_self, RingHom.id_apply] using h.2
    obtain ⟨c, hc0, hcle⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h1 h2
    have hle : ‖T‖ ≤ ‖T‖ - c := by
      calc
        ‖T‖ = ⨆ x, |T.rayleighQuotient x| := T.norm_eq_iSup_rayleighQuotient hs
        _ ≤ ‖T‖ - c := ciSup_le hcle
    linarith
  have heigen (t : ℝ) (ht : t ≠ 0) (htspec : t ∈ spectrum ℝ T) :
      |t| ^ 3 ≤ 4 * Graphon.cutNormDiff U W := by
    obtain ⟨v, hv⟩ := ((hc.hasEigenvalue_iff_mem_spectrum ht).mpr htspec).exists_hasEigenvector
    let f := ‖v‖⁻¹ • v
    have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
    have hfnorm : ‖f‖ = 1 := by
      simp [f, norm_smul, hv0]
    apply graphonDifference_eigenvalue_cube_le U W f t ht hfnorm
    change T (‖v‖⁻¹ • v) = t • (‖v‖⁻¹ • v)
    have hveq : T v = t • v := hv.apply_eq_smul
    rw [map_smul, hveq, smul_smul, smul_smul, mul_comm]
  rcases hspec with h | h
  · simpa only [abs_of_nonneg (norm_nonneg T)] using heigen ‖T‖ hT h
  · simpa only [abs_neg, abs_of_nonneg (norm_nonneg T)] using
      heigen (-‖T‖) (neg_ne_zero.mpr hT) h

/-- The rectangle cut norm of a real kernel, using the original measure. -/
def kernelCutNorm (K : Ω → Ω → ℝ) : ℝ :=
  ⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
    |∫ z in S ×ˢ T, K z.1 z.2 ∂μ.prod μ|

omit [IsProbabilityMeasure μ] in
theorem kernelCutNorm_nonneg (K : Ω → Ω → ℝ) : 0 ≤ kernelCutNorm (μ := μ) K := by
  apply Real.iSup_nonneg
  intro S
  apply Real.iSup_nonneg
  intro _
  apply Real.iSup_nonneg
  intro T
  apply Real.iSup_nonneg
  intro _
  exact abs_nonneg _

omit [IsProbabilityMeasure μ] in
theorem kernelCutNorm_congr {K L : Ω → Ω → ℝ}
    (h : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = L z.1 z.2) :
    kernelCutNorm (μ := μ) K = kernelCutNorm (μ := μ) L := by
  unfold kernelCutNorm
  congr 1
  funext S
  congr 1
  funext hS
  congr 1
  funext T
  congr 1
  funext hT
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae h)

omit [IsProbabilityMeasure μ] in
theorem kernelCutNorm_const_mul (K : Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    kernelCutNorm (μ := μ) (fun x y => c * K x y) = c * kernelCutNorm (μ := μ) K := by
  unfold kernelCutNorm
  simp_rw [integral_const_mul, abs_mul, abs_of_nonneg hc,
    Real.mul_iSup_of_nonneg hc]

private def graphonOfKernel (K : Ω → Ω → ℝ)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (hbound : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 ∈ Set.Icc 0 1) : Graphon Ω μ where
  toAEEqFun := AEEqFun.mk (fun z : Ω × Ω => K z.1 z.2) hK
  symm' := by
    have heq := AEEqFun.coeFn_mk (fun z : Ω × Ω => K z.1 z.2) hK
    filter_upwards [heq, ae_prod_swap heq, hsym] with z hz hswap hs
    exact hswap.trans (hs.symm.trans hz.symm)
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_mk (fun z : Ω × Ω => K z.1 z.2) hK, hbound] with z hz hb
    rwa [hz]

private theorem graphonOfKernel_coe (K : Ω → Ω → ℝ)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (hbound : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 ∈ Set.Icc 0 1) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, (graphonOfKernel K hK hsym hbound).toAEEqFun z = K z.1 z.2 :=
  AEEqFun.coeFn_mk _ _

/-- The cubic operator estimate for an arbitrary symmetric
measurable kernel bounded by a positive constant. The graphon adapter and
cut-norm scaling are proved within the argument. -/
theorem operator_norm_cube_le_cutNorm
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 < B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1) :
    ‖operator K hB0.le hK hB‖ ^ 3 ≤ 4 * B ^ 2 * kernelCutNorm (μ := μ) K := by
  let P := fun x y => (K x y / B + 1) / 2
  let Q := fun x y => (1 - K x y / B) / 2
  have hP : AEStronglyMeasurable (fun z : Ω × Ω => P z.1 z.2) (μ.prod μ) := by
    simpa only [P, div_eq_mul_inv] using ((hK.mul_const B⁻¹).add_const 1).mul_const (2⁻¹ : ℝ)
  have hQ : AEStronglyMeasurable (fun z : Ω × Ω => Q z.1 z.2) (μ.prod μ) := by
    simpa only [Q, div_eq_mul_inv, sub_eq_neg_add, Pi.neg_apply] using
      ((hK.mul_const B⁻¹).neg.add_const 1).mul_const (2⁻¹ : ℝ)
  have hPs : ∀ᵐ z : Ω × Ω ∂μ.prod μ, P z.1 z.2 = P z.2 z.1 := by
    filter_upwards [hsym] with z hz
    simp only [P, hz]
  have hQs : ∀ᵐ z : Ω × Ω ∂μ.prod μ, Q z.1 z.2 = Q z.2 z.1 := by
    filter_upwards [hsym] with z hz
    simp only [Q, hz]
  have hPb : ∀ᵐ z : Ω × Ω ∂μ.prod μ, P z.1 z.2 ∈ Set.Icc 0 1 := by
    filter_upwards [hB] with z hz
    have h : |K z.1 z.2 / B| ≤ 1 := by
      rw [abs_div, abs_of_pos hB0]
      exact (div_le_one hB0).mpr (by simpa only [Real.norm_eq_abs] using hz)
    dsimp [P]
    constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  have hQb : ∀ᵐ z : Ω × Ω ∂μ.prod μ, Q z.1 z.2 ∈ Set.Icc 0 1 := by
    filter_upwards [hB] with z hz
    have h : |K z.1 z.2 / B| ≤ 1 := by
      rw [abs_div, abs_of_pos hB0]
      exact (div_le_one hB0).mpr (by simpa only [Real.norm_eq_abs] using hz)
    dsimp [Q]
    constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  let U := graphonOfKernel P hP hPs hPb
  let W := graphonOfKernel Q hQ hQs hQb
  have heq : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      K z.1 z.2 = B * graphonDifference U W z.1 z.2 := by
    filter_upwards [graphonOfKernel_coe P hP hPs hPb,
      graphonOfKernel_coe Q hQ hQs hQb] with z hp hq
    change K z.1 z.2 = B * (U.toAEEqFun z - W.toAEEqFun z)
    rw [hp, hq]
    dsimp [P, Q]
    field_simp
    ring
  have hop : operator K hB0.le hK hB = B • graphonDifferenceOperator U W := by
    apply ContinuousLinearMap.ext
    intro f
    apply ext_inner_right ℝ
    intro g
    rw [smul_apply, real_inner_smul_left,
      operator_inner K hB0.le hK hB]
    change _ = B * ⟪operator (graphonDifference U W) (by norm_num)
      (graphonDifference_measurable U W) (graphonDifference_bound U W) f, g⟫
    rw [operator_inner, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz]
    ring
  have hcut : kernelCutNorm (μ := μ) K = B * Graphon.cutNormDiff U W := by
    calc
      _ = kernelCutNorm (μ := μ) (fun x y => B * graphonDifference U W x y) :=
        kernelCutNorm_congr heq
      _ = B * kernelCutNorm (μ := μ) (graphonDifference U W) :=
        kernelCutNorm_const_mul _ B hB0.le
      _ = B * Graphon.cutNormDiff U W := rfl
  rw [hop, norm_smul, Real.norm_eq_abs, abs_of_pos hB0, mul_pow, hcut]
  have h := mul_le_mul_of_nonneg_left
    (graphonDifferenceOperator_norm_cube_le U W) (pow_nonneg hB0.le 3)
  nlinarith

end Erdos1017.KernelOperator
