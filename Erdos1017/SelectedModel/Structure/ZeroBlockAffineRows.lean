module

public import Erdos1017.Models.Kernel.FeatureKernel
public import Erdos1017.Models.Kernel.BoundedPositiveIndex
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Probability.ConditionalProbability

/-!
# Affine rows on a zero block

An integrable Hilbert feature with zero pair Gram form vanishes almost
everywhere, a rank-two affine Gram identity forces the feature to be affine in
the scalar coordinate, and a zero block in the canonical kernel therefore has
affine whole rows with coefficients built from integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace ENNReal ProbabilityTheory

namespace Erdos1017.KernelOperator

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure Ω}

/-- An integrable Hilbert feature with zero pair Gram form vanishes almost
everywhere. Set integrals, rather than pointwise diagonal values, detect it. -/
theorem ae_zero_of_ae_pair_inner_zero (F : Ω → H) (hF : Integrable F μ)
    (hzero : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ⟪F x, F y⟫ = 0) : F =ᵐ[μ] 0 := by
  apply hF.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s _ _
  let w := ∫ x in s, F x ∂μ
  have hrow : ∀ᵐ x ∂μ, ⟪F x, w⟫ = 0 := by
    filter_upwards [hzero] with x hx
    dsimp only [w]
    rw [← integral_inner hF.integrableOn]
    exact integral_eq_zero_of_ae
      (hx.filter_mono ae_restrict_le)
  have hw : ⟪w, w⟫ = 0 := by
    dsimp only [w]
    rw [← integral_inner hF.integrableOn]
    apply integral_eq_zero_of_ae
    filter_upwards [hrow.filter_mono ae_restrict_le] with x hx
    simpa only [w, real_inner_comm, Pi.zero_apply] using hx
  exact inner_self_eq_zero.mp hw

private theorem gram_row_integral
    (V : Ω → H) (φ : Ω → ℝ) (ν σ : ℝ)
    (hgram : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ⟪V x, V y⟫ = ν + σ * φ x * φ y)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hφf : Integrable (fun x => φ x * f x) μ)
    (hfV : Integrable (fun x => f x • V x) μ) :
    ∀ᵐ x ∂μ, ⟪V x, ∫ y, f y • V y ∂μ⟫ =
      ν * (∫ y, f y ∂μ) + (σ * φ x) * (∫ y, φ y * f y ∂μ) := by
  filter_upwards [hgram] with x hx
  calc
    ⟪V x, ∫ y, f y • V y ∂μ⟫ = ∫ y, ⟪V x, f y • V y⟫ ∂μ :=
      (integral_inner hfV _).symm
    _ = ∫ y, ν * f y + (σ * φ x) * (φ y * f y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      rw [real_inner_smul_right, hy]
      ring
    _ = ν * (∫ y, f y ∂μ) + (σ * φ x) * (∫ y, φ y * f y ∂μ) := by
      rw [integral_add (hf.const_mul _) (hφf.const_mul _),
        integral_const_mul, integral_const_mul]

variable [IsProbabilityMeasure μ]

/-- A rank-two affine Gram identity forces the actual Hilbert feature to
be affine in the scalar coordinate. Both coefficients are constructed
from its mean and centered first moment, including zero variance. -/
theorem exists_affine_feature_of_ae_gram
    (V : Ω → H) (hV : AEStronglyMeasurable V μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖V x‖ ≤ B)
    (φ : Ω → ℝ) (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) (ν σ : ℝ)
    (hgram : ∀ᵐ p ∂μ.prod μ, ⟪V p.1, V p.2⟫ = ν + σ * φ p.1 * φ p.2) :
    ∃ a b : H, ∀ᵐ x ∂μ, V x = a + φ x • b := by
  have hiV : Integrable V μ := (MemLp.of_bound hV B hB (p := 1)).integrable le_rfl
  have hiφ : Integrable φ μ := (MemLp.of_bound hφ C hC (p := 1)).integrable le_rfl
  let q := ∫ x, φ x ∂μ
  let ψ := fun x => φ x - q
  let a := ∫ x, V x ∂μ
  have hψ : AEStronglyMeasurable ψ μ := hφ.sub aestronglyMeasurable_const
  have hψB : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C + ‖q‖ := by
    filter_upwards [hC] with x hx
    exact (norm_sub_le _ _).trans (add_le_add hx le_rfl)
  have hiψ : Integrable ψ μ := hiφ.sub (integrable_const q)
  have hiψsq : Integrable (fun x => ψ x ^ 2) μ :=
    (MemLp.of_bound hψ _ hψB (p := 2)).integrable_sq
  have hiφψ : Integrable (fun x => φ x * ψ x) μ := hiψ.bdd_mul hφ hC
  have hiψV : Integrable (fun x => ψ x • V x) μ := hiV.bdd_smul _ hψ hψB
  have hψzero : (∫ x, ψ x ∂μ) = 0 := by
    dsimp only [ψ, q]
    rw [integral_sub hiφ (integrable_const _)]
    simp
  let s := ∫ x, ψ x ^ 2 ∂μ
  have hmoment : (∫ x, φ x * ψ x ∂μ) = s := by
    calc
      (∫ x, φ x * ψ x ∂μ) = ∫ x, ψ x ^ 2 + q * ψ x ∂μ := by
        apply integral_congr_ae
        exact .of_forall (fun x => by
          dsimp only [ψ]
          ring)
      _ = s := by
        rw [integral_add hiψsq (hiψ.const_mul _), integral_const_mul, hψzero]
        simp only [mul_zero, add_zero, s]
  have hgram' := Measure.ae_ae_of_ae_prod hgram
  have harow : ∀ᵐ x ∂μ, ⟪V x, a⟫ = ν + σ * φ x * q := by
    simpa [a, q, measureReal_def]
      using gram_row_integral V φ ν σ hgram' (fun _ => 1) (integrable_const 1)
        (by simpa only [mul_one] using hiφ) (by simpa only [one_smul] using hiV)
  by_cases hs : s = 0
  · have hψae : ∀ᵐ x ∂μ, ψ x = 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (.of_forall (fun x => sq_nonneg (ψ x))) hiψsq).mp hs
      exact hz.mono (fun x hx => sq_eq_zero_iff.mp hx)
    let F := fun x => V x - a
    have hiF : Integrable F μ := hiV.sub (integrable_const a)
    have hFV : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ⟪F x, V y⟫ = 0 := by
      filter_upwards [hgram', hψae] with x hx hψx
      filter_upwards [hx, harow] with y hxy hay
      dsimp only [F]
      rw [inner_sub_left, real_inner_comm (V y) a, hay, hxy]
      have hφx : φ x = q := sub_eq_zero.mp hψx
      rw [hφx]
      ring
    have hFa : ∀ᵐ x ∂μ, ⟪F x, a⟫ = 0 := by
      filter_upwards [hFV] with x hx
      dsimp only [a]
      rw [← integral_inner hiV]
      exact integral_eq_zero_of_ae hx
    have hFF : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ⟪F x, F y⟫ = 0 := by
      filter_upwards [hFV, hFa] with x hx ha
      filter_upwards [hx] with y hy
      simpa only [F, inner_sub_right, ha, sub_zero] using hy
    have hFzero := ae_zero_of_ae_pair_inner_zero F hiF hFF
    refine ⟨a, 0, ?_⟩
    filter_upwards [hFzero] with x hx
    simpa only [smul_zero, add_zero] using sub_eq_zero.mp hx
  · let b := s⁻¹ • (∫ x, ψ x • V x ∂μ)
    have hbrow : ∀ᵐ x ∂μ, ⟪V x, b⟫ = σ * φ x := by
      have hrow := gram_row_integral V φ ν σ hgram' ψ hiψ hiφψ hiψV
      filter_upwards [hrow] with x hx
      dsimp only [b]
      rw [real_inner_smul_right, hx, hψzero, hmoment]
      field_simp
      ring
    let F := fun x => V x - a - ψ x • b
    have hiF : Integrable F μ := (hiV.sub (integrable_const a)).sub (hiψ.smul_const b)
    have hFV : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ⟪F x, V y⟫ = 0 := by
      filter_upwards [hgram'] with x hx
      filter_upwards [hx, harow, hbrow] with y hxy hay hby
      dsimp only [F]
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left,
        real_inner_comm (V y) a, hay, real_inner_comm (V y) b, hby, hxy]
      dsimp only [ψ]
      ring
    have hFa : ∀ᵐ x ∂μ, ⟪F x, a⟫ = 0 := by
      filter_upwards [hFV] with x hx
      dsimp only [a]
      rw [← integral_inner hiV]
      exact integral_eq_zero_of_ae hx
    have hFb : ∀ᵐ x ∂μ, ⟪F x, b⟫ = 0 := by
      filter_upwards [hFV] with x hx
      dsimp only [b]
      rw [real_inner_smul_right, ← integral_inner hiψV]
      have hz : (∫ y, ⟪F x, ψ y • V y⟫ ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hx] with y hy
        simp only [real_inner_smul_right, hy, mul_zero, Pi.zero_apply]
      rw [hz, mul_zero]
    have hFF : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ⟪F x, F y⟫ = 0 := by
      filter_upwards [hFV, hFa, hFb] with x hx ha hb
      filter_upwards [hx] with y hy
      dsimp only [F]
      rw [inner_sub_right, inner_sub_right, real_inner_smul_right, ha, hb]
      simpa only [mul_zero, sub_zero] using hy
    have hFzero := ae_zero_of_ae_pair_inner_zero F hiF hFF
    refine ⟨a - q • b, b, ?_⟩
    filter_upwards [hFzero] with x hx
    have heq : V x = a + ψ x • b := by
      have heq : V x - a = ψ x • b := sub_eq_zero.mp hx
      exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
    rw [heq]
    dsimp only [ψ]
    module

/-- The feature factorization on a positive-measure block is derived from
its actual restricted pair Gram identity by conditioning the block law. -/
theorem exists_affine_feature_on_set_of_ae_gram
    (E : Set Ω) (hE : MeasurableSet E) (hEpos : μ E ≠ 0)
    (V : Ω → H) (hV : AEStronglyMeasurable V μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖V x‖ ≤ B)
    (φ : Ω → ℝ) (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) (ν σ : ℝ)
    (hgram : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E),
      ⟪V p.1, V p.2⟫ = ν + σ * φ p.1 * φ p.2) :
    ∃ a b : H, ∀ᵐ x ∂μ, x ∈ E → V x = a + φ x • b := by
  let η := ProbabilityTheory.cond μ E
  have : IsProbabilityMeasure η := ProbabilityTheory.cond_isProbabilityMeasure hEpos
  have hac : η ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hacE : η ≪ μ.restrict E := Measure.smul_absolutelyContinuous
  obtain ⟨a, b, hab⟩ := exists_affine_feature_of_ae_gram (μ := η)
    V (AEStronglyMeasurable.mono_ac hac hV) (hac.ae_le hB)
    φ (AEStronglyMeasurable.mono_ac hac hφ) (hac.ae_le hC) ν σ
    ((hacE.prod hacE).ae_le hgram)
  refine ⟨a, b, (ae_restrict_iff' hE).mp ?_⟩
  exact (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.inv_ne_zero.mpr (measure_ne_top μ E))).mp hab

/-- A genuine zero block in the displayed canonical kernel has affine
whole rows. The feature coefficients and bounded L² rows are constructed
from actual integrals, without a supplied pointwise isometry. -/
theorem exists_affine_rows_of_zero_block
    (K : Ω → Ω → ℝ) (E : Set Ω) (hE : MeasurableSet E) (hEpos : μ E ≠ 0)
    (V : Ω → H) (hV : AEStronglyMeasurable V μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖V x‖ ≤ B)
    (φ : Ω → ℝ) (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖φ x‖ ≤ C) (ν σ : ℝ)
    (hrep : ∀ᵐ p ∂μ.prod μ,
      K p.1 p.2 = ν + σ * φ p.1 * φ p.2 - ⟪V p.1, V p.2⟫)
    (hzero : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E), K p.1 p.2 = 0) :
    ∃ P R : Lp ℝ 2 μ, P ∈ boundedL2Submodule μ ∧ R ∈ boundedL2Submodule μ ∧
      ∀ᵐ x ∂μ, x ∈ E → ∀ᵐ y ∂μ, K x y = P y + φ x * R y := by
  have hac : μ.restrict E ≪ μ := Measure.restrict_le_self.absolutelyContinuous
  have hgram : ∀ᵐ p ∂(μ.restrict E).prod (μ.restrict E),
      ⟪V p.1, V p.2⟫ = ν + σ * φ p.1 * φ p.2 := by
    filter_upwards [(hac.prod hac).ae_le hrep, hzero] with p hp hz
    linarith
  obtain ⟨a, b, hab⟩ := exists_affine_feature_on_set_of_ae_gram
    E hE hEpos V hV hB φ hφ hC ν σ hgram
  let p := fun y => ν - ⟪a, V y⟫
  let r := fun y => σ * φ y - ⟪b, V y⟫
  let Bp := ‖ν‖ + ‖a‖ * |B|
  let Br := ‖σ‖ * |C| + ‖b‖ * |B|
  have hp : AEStronglyMeasurable p μ :=
    aestronglyMeasurable_const.sub (aestronglyMeasurable_const.inner hV)
  have hr : AEStronglyMeasurable r μ :=
    (hφ.const_mul σ).sub (aestronglyMeasurable_const.inner hV)
  have hpB : ∀ᵐ y ∂μ, ‖p y‖ ≤ Bp := by
    filter_upwards [hB] with y hy
    calc
      ‖p y‖ ≤ ‖ν‖ + ‖⟪a, V y⟫‖ := norm_sub_le _ _
      _ ≤ ‖ν‖ + ‖a‖ * |B| := by
        gcongr
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hy.trans (le_abs_self B)) (norm_nonneg a))
  have hrB : ∀ᵐ y ∂μ, ‖r y‖ ≤ Br := by
    filter_upwards [hB, hC] with y hy hφy
    calc
      ‖r y‖ ≤ ‖σ * φ y‖ + ‖⟪b, V y⟫‖ := norm_sub_le _ _
      _ ≤ ‖σ‖ * |C| + ‖b‖ * |B| := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hφy.trans (le_abs_self C)) (norm_nonneg σ)
        · exact (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hy.trans (le_abs_self B)) (norm_nonneg b))
  have hpmem : MemLp p 2 μ := MemLp.of_bound hp Bp hpB
  have hrmem : MemLp r 2 μ := MemLp.of_bound hr Br hrB
  let P := hpmem.toLp p
  let R := hrmem.toLp r
  refine ⟨P, R, ?_, ?_, ?_⟩
  · refine ⟨Bp, by positivity, ?_⟩
    filter_upwards [hpmem.coeFn_toLp, hpB] with y hy hbound
    rwa [hy]
  · refine ⟨Br, by positivity, ?_⟩
    filter_upwards [hrmem.coeFn_toLp, hrB] with y hy hbound
    rwa [hy]
  · filter_upwards [hab, Measure.ae_ae_of_ae_prod hrep] with x hx hrow hxe
    filter_upwards [hrow, hpmem.coeFn_toLp, hrmem.coeFn_toLp] with y hxy hpy hry
    rw [hpy, hry, hxy, hx hxe]
    dsimp only [p, r]
    rw [inner_add_left, real_inner_smul_left]
    ring

end Erdos1017.KernelOperator
