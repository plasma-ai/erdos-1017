module

public import Erdos1017.Models.Kernel.FeatureDiagonal
public import Erdos1017.Models.Kernel.PositiveSpectralSubspace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The spectral trace and its bounds

A bounded feature with normalized spectral coordinates has absolutely summable
eigenvalues, integrating the canonical signed diagonal recovers the spectral
trace, and the absolute spectral sum of a bounded nonnegative symmetric kernel
is at most twice its positive rank times the kernel bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem integral_basis_sq (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (i : ι) :
    (∫ x, (b i x) ^ 2 ∂μ) = 1 := by
  have hi : ⟪b i, b i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]
    norm_num
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, ← pow_two] using hi

/-- The absolute spectral energy is the squared norm of its actual feature. -/
theorem feature_absolute_energy (t a : ι → ℝ) (F : lp (fun _ : ι => ℝ) 2)
    (hcoord : ∀ i, F i = Real.sqrt |t i| * a i) :
    Summable (fun i => |t i| * (a i) ^ 2) ∧
      (∑' i, |t i| * (a i) ^ 2) = ‖F‖ ^ 2 := by
  have heq (i : ι) : ⟪F i, F i⟫ = |t i| * (a i) ^ 2 := by
    rw [RCLike.inner_apply]
    simp only [conj_trivial, hcoord]
    calc
      (Real.sqrt |t i| * a i) * (Real.sqrt |t i| * a i) =
          (Real.sqrt |t i|) ^ 2 * (a i) ^ 2 := by ring
      _ = |t i| * (a i) ^ 2 := by rw [Real.sq_sqrt (abs_nonneg _)]
  constructor
  · exact (lp.summable_inner F F).congr heq
  · calc
      (∑' i, |t i| * (a i) ^ 2) = ∑' i, inner ℝ (F i) (F i) :=
        tsum_congr (fun i => (heq i).symm)
      _ = ⟪F, F⟫ := (lp.inner_eq_tsum F F).symm
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F

/-- A bounded feature with normalized spectral coordinates has absolutely
summable eigenvalues. The proof integrates finite coordinate energies. -/
theorem summable_abs_eigenvalues_of_feature
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (F : Ω → lp (fun _ : ι => ℝ) 2) (R : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ R)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x) :
    Summable (fun i => |t i|) := by
  apply summable_of_sum_le (fun i => abs_nonneg (t i)) (c := R ^ 2)
  intro s
  have hi (i : ι) : Integrable (fun x => (b i x) ^ 2) μ := by
    exact ((Lp.memLp (b i)).integrable_mul (Lp.memLp (b i))).congr
      (Filter.Eventually.of_forall (fun x => by simp only [Pi.mul_apply, pow_two]))
  have hsum : Integrable (fun x => ∑ i ∈ s, |t i| * (b i x) ^ 2) μ :=
    integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hle : ∀ᵐ x ∂μ, (∑ i ∈ s, |t i| * (b i x) ^ 2) ≤ R ^ 2 := by
    filter_upwards [hbound, hcoord] with x hx hc
    obtain ⟨hs, he⟩ := feature_absolute_energy t (fun i => b i x) (F x) hc
    calc
      (∑ i ∈ s, |t i| * (b i x) ^ 2) ≤ ∑' i, |t i| * (b i x) ^ 2 :=
        hs.sum_le_tsum s (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      _ = ‖F x‖ ^ 2 := he
      _ ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h := integral_mono_ae hsum (integrable_const (R ^ 2)) hle
  simpa only [integral_finsetSum _ (fun i _ => (hi i).const_mul _),
    integral_const_mul, integral_basis_sq, mul_one, integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using h

/-- Integrating the canonical signed diagonal recovers the spectral trace.
The product-almost-everywhere kernel bounds therefore bound that trace. -/
theorem spectral_trace_bounds [Countable ι]
    (K : Ω → Ω → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (F : Ω → lp (fun _ : ι => ℝ) 2) (hF : AEStronglyMeasurable F μ)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ R)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x)
    (hrepresentation : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫)
    (B : ℝ) (hK : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z.1 z.2 ∧ K z.1 z.2 ≤ B) :
    0 ≤ (∑' i, t i) ∧ (∑' i, t i) ≤ B := by
  have habs := summable_abs_eigenvalues_of_feature b t F R hbound hcoord
  have hi (i : ι) : Integrable (fun x => t i * (b i x) ^ 2) μ := by
    exact (show Integrable (fun x => (b i x) ^ 2) μ by
      exact ((Lp.memLp (b i)).integrable_mul (Lp.memLp (b i))).congr
        (Filter.Eventually.of_forall (fun x => by simp only [Pi.mul_apply, pow_two]))).const_mul _
  have hnorm (i : ι) : (∫ x, ‖t i * (b i x) ^ 2‖ ∂μ) = |t i| := by
    simp_rw [norm_mul, Real.norm_eq_abs, abs_sq]
    rw [integral_const_mul, integral_basis_sq, mul_one]
  have htrace : (∑' i, t i) = ∫ x, (∑' i, t i * (b i x) ^ 2) ∂μ := by
    have h := integral_tsum_of_summable_integral_norm hi (by simpa only [hnorm] using habs)
    simpa only [integral_const_mul, integral_basis_sq, mul_one] using h
  have hdiag := spectral_diagonal_bounds K t (fun i => (b i : Ω → ℝ)) F hF
    hcoord hrepresentation B hK
  have hdiagEq : (fun x => ∑' i, t i * (b i x) ^ 2) =ᵐ[μ]
      (fun x => ⟪spectralSign t (F x), F x⟫) := by
    filter_upwards [hcoord] with x hc
    rw [spectralSign_inner_eq_tsum t (fun i => b i x) (fun i => b i x) (F x) (F x) hc hc]
    exact tsum_congr (fun i => by ring)
  have hdi : Integrable (fun x => ⟪spectralSign t (F x), F x⟫) μ := by
    exact (show MemLp (fun x => ⟪spectralSign t (F x), F x⟫) 1 μ from
      MemLp.of_bound (((spectralSign t).continuous.comp_aestronglyMeasurable hF).inner hF)
        (R ^ 2) (by
          filter_upwards [hbound] with x hx
          calc
            ‖⟪spectralSign t (F x), F x⟫‖ ≤ ‖spectralSign t (F x)‖ * ‖F x‖ :=
              norm_inner_le_norm _ _
            _ = ‖F x‖ * ‖F x‖ := by rw [(spectralSign t).norm_map]
            _ ≤ R * R := mul_le_mul hx hx (norm_nonneg _) hR
            _ = R ^ 2 := by ring)).integrable le_rfl
  rw [htrace]
  constructor
  · exact integral_nonneg_of_ae (hdiag.mono (fun _ hx => hx.1))
  · simpa using integral_mono_ae (hdi.congr hdiagEq.symm) (integrable_const B)
      (hdiag.mono (fun _ hx => hx.2))

/-- A nonnegative signed sum bounds the absolute sum by twice its finite
positive part. -/
theorem absolute_sum_le_twice_positive (t : ι → ℝ) (s : Finset ι)
    (hinside : ∀ i ∈ s, 0 ≤ t i) (houtside : ∀ i ∉ s, t i ≤ 0)
    (habs : Summable (fun i => |t i|)) (htrace : 0 ≤ ∑' i, t i) :
    (∑' i, |t i|) ≤ 2 * ∑ i ∈ s, t i := by
  classical
  let p : ι → ℝ := fun i => if i ∈ s then t i else 0
  have hpzero : ∀ i ∉ s, p i = 0 := fun i hi => by simp [p, hi]
  have hp : Summable p := summable_of_ne_finset_zero hpzero
  have ht : Summable t := summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using habs)
  have heq : (fun i => |t i|) = (fun i => 2 * p i - t i) := by
    funext i
    by_cases hi : i ∈ s
    · simp only [p, ite_eq_left hi, abs_of_nonneg (hinside i hi)]
      ring
    · simp [p, hi, abs_of_nonpos (houtside i hi)]
  rw [heq, (hp.mul_left 2).tsum_sub ht, tsum_mul_left, tsum_eq_sum hpzero]
  have hpsum : (∑ i ∈ s, p i) = ∑ i ∈ s, t i := by simp [p]
  rw [hpsum]
  linarith

/-- The absolute spectral sum of a bounded nonnegative symmetric kernel is
at most twice its positive rank times the kernel bound. This supplies the
numerical trace bound used by stabilization without assuming trace class. -/
theorem summable_spectral_abs_and_bound [Countable ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s : Finset ι) (hinside : ∀ i ∈ s, 0 < t i) (houtside : ∀ i ∉ s, t i ≤ 0) :
    Summable (fun i => |t i|) ∧ (∑' i, |t i|) ≤ 2 * s.card * B := by
  obtain ⟨F, hF, hbound, hcoord, hrepresentation⟩ :=
    exists_bounded_spectral_feature K hB0 hK hB hK0 hsym b t heigen s hinside houtside
  have habs := summable_abs_eigenvalues_of_feature b t F _ hbound hcoord
  have htrace := spectral_trace_bounds K b t F hF _ (Real.sqrt_nonneg _) hbound hcoord
    hrepresentation B (by
      filter_upwards [hK0, hB] with z hz hb
      exact ⟨hz, (le_abs_self _).trans hb⟩)
  refine ⟨habs, (absolute_sum_le_twice_positive t s (fun i hi => (hinside i hi).le)
    houtside habs htrace.1).trans ?_⟩
  have ht (i : ι) : t i ≤ B := by
    have h := onL2_norm_le K hB0 hK hB (b i)
    change ‖operator K hB0 hK hB (b i)‖ ≤ B * ‖b i‖ at h
    rw [heigen i, norm_smul, b.orthonormal.norm_eq_one, mul_one, mul_one,
      Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hsum : (∑ i ∈ s, t i) ≤ s.card * B := by
    simpa using Finset.sum_le_sum (s := s) (fun i _ => ht i)
  nlinarith

end Erdos1017.KernelOperator
