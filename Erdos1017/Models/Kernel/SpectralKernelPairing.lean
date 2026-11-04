module

public import Erdos1017.Models.Kernel.SpectralTrace

/-!
# Pairing bounded kernels with spectral kernels

Pairing a bounded kernel with an absolutely summable spectral kernel equals the
sum of its operator matrix coefficients, and this pairing is bounded by the
operator norm times the absolute spectral sum, with no trace-class structure
assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A normalized L2 vector gives a unit bound on the integral of the
absolute value of its rank-one kernel. -/
theorem integral_norm_rank_one_le_one (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (i : ι) :
    (∫ z : Ω × Ω, ‖b i z.1‖ * ‖b i z.2‖ ∂μ.prod μ) ≤ 1 := by
  rw [integral_prod_mul (μ := μ) (ν := μ) (fun x => ‖b i x‖) (fun x => ‖b i x‖)]
  have h := integral_norm_le_L2 (b i)
  rw [b.orthonormal.norm_eq_one] at h
  have hn : 0 ≤ ∫ x, ‖b i x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  nlinarith

/-- Bounded kernels pair absolutely with each spectral rank-one kernel.
The summable majorant depends on the eigenvalue, rather than on pointwise
eigenfunction bounds. -/
theorem integral_norm_spectral_term_le
    (H : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hH : AEStronglyMeasurable (fun z : Ω × Ω => H z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖H z.1 z.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ) (i : ι) :
    (∫ z : Ω × Ω, ‖H z.1 z.2 * (t i * b i z.1 * b i z.2)‖ ∂μ.prod μ) ≤
      B * |t i| := by
  have hbi := (Lp.memLp (b i)).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hi : Integrable (fun z : Ω × Ω => H z.1 z.2 * (t i * b i z.1 * b i z.2))
      (μ.prod μ) := by
    convert (integrable_bilinear hH hB (b i) (b i)).const_mul (t i) using 1
    funext z
    ring
  have hm : Integrable (fun z : Ω × Ω => (B * |t i|) * (‖b i z.1‖ * ‖b i z.2‖))
      (μ.prod μ) := (hbi.norm.mul_prod hbi.norm).const_mul _
  calc
    (∫ z : Ω × Ω, ‖H z.1 z.2 * (t i * b i z.1 * b i z.2)‖ ∂μ.prod μ) ≤
        ∫ z : Ω × Ω, (B * |t i|) * (‖b i z.1‖ * ‖b i z.2‖) ∂μ.prod μ := by
      apply integral_mono_ae hi.norm hm
      filter_upwards [hB] with z hz
      simp only [norm_mul, Real.norm_eq_abs] at hz ⊢
      calc
        |H z.1 z.2| * (|t i| * |b i z.1| * |b i z.2|) ≤
            B * (|t i| * |b i z.1| * |b i z.2|) :=
          mul_le_mul_of_nonneg_right hz (by positivity)
        _ = B * |t i| * (|b i z.1| * |b i z.2|) := by ring
    _ = (B * |t i|) * ∫ z : Ω × Ω, ‖b i z.1‖ * ‖b i z.2‖ ∂μ.prod μ :=
      integral_const_mul _ _
    _ ≤ B * |t i| := by
      simpa using mul_le_mul_of_nonneg_left (integral_norm_rank_one_le_one b i)
        (mul_nonneg hB0 (abs_nonneg _))

/-- Pairing a bounded kernel with an actual absolutely summable spectral
kernel equals the sum of its operator matrix coefficients. -/
theorem integral_spectral_pairing [Countable ι]
    (H K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hH : AEStronglyMeasurable (fun z : Ω × Ω => H z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖H z.1 z.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (ht : Summable (fun i => |t i|))
    (hrepresentation : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ∑' i, t i * b i z.1 * b i z.2) :
    (∫ z : Ω × Ω, H z.1 z.2 * K z.1 z.2 ∂μ.prod μ) =
      ∑' i, t i * ⟪operator H hB0 hH hB (b i), b i⟫ := by
  have hi (i : ι) : Integrable
      (fun z : Ω × Ω => H z.1 z.2 * (t i * b i z.1 * b i z.2)) (μ.prod μ) := by
    convert (integrable_bilinear hH hB (b i) (b i)).const_mul (t i) using 1
    funext z
    ring
  have hs : Summable (fun i => ∫ z : Ω × Ω,
      ‖H z.1 z.2 * (t i * b i z.1 * b i z.2)‖ ∂μ.prod μ) :=
    (ht.mul_left B).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      (integral_norm_spectral_term_le H hB0 hH hB b t)
  calc
    (∫ z : Ω × Ω, H z.1 z.2 * K z.1 z.2 ∂μ.prod μ) =
        ∫ z : Ω × Ω, ∑' i, H z.1 z.2 * (t i * b i z.1 * b i z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [hrepresentation] with z hz
      rw [hz, tsum_mul_left]
    _ = ∑' i, ∫ z : Ω × Ω, H z.1 z.2 * (t i * b i z.1 * b i z.2) ∂μ.prod μ :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑' i, t i * ⟪operator H hB0 hH hB (b i), b i⟫ := by
      apply tsum_congr
      intro i
      rw [operator_inner, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)

/-- The diagonal coefficient of an operator in a normalized Hilbert basis
is controlled by its operator norm. -/
theorem norm_basis_operator_inner_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E) (i : ι) :
    ‖⟪T (b i), b i⟫‖ ≤ ‖T‖ := by
  calc
    ‖⟪T (b i), b i⟫‖ ≤ ‖T (b i)‖ * ‖b i‖ := norm_inner_le_norm _ _
    _ ≤ ‖T‖ := by simpa only [b.orthonormal.norm_eq_one, mul_one] using T.le_opNorm (b i)

/-- The actual kernel pairing is bounded by the operator norm and the
absolute spectral sum. No trace-class structure is assumed. -/
theorem norm_integral_spectral_pairing_le [Countable ι]
    (H K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hH : AEStronglyMeasurable (fun z : Ω × Ω => H z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z ∂μ.prod μ, ‖H z.1 z.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (ht : Summable (fun i => |t i|))
    (hrepresentation : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ∑' i, t i * b i z.1 * b i z.2) :
    ‖∫ z : Ω × Ω, H z.1 z.2 * K z.1 z.2 ∂μ.prod μ‖ ≤
      ‖operator H hB0 hH hB‖ * ∑' i, |t i| := by
  let T := operator H hB0 hH hB
  have hle (i : ι) : ‖t i * ⟪T (b i), b i⟫‖ ≤ ‖T‖ * |t i| := by
    rw [norm_mul, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (norm_basis_operator_inner_le b T i) (abs_nonneg (t i))
  have hs : Summable (fun i => ‖t i * ⟪T (b i), b i⟫‖) :=
    (ht.mul_left ‖T‖).of_nonneg_of_le (fun _ => norm_nonneg _) hle
  rw [integral_spectral_pairing H K hB0 hH hB b t ht hrepresentation]
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum hle (ht.mul_left ‖T‖)).trans_eq (tsum_mul_left))

/-- Spectral features supply the pointwise series used in the pairing
estimate, with one common product-almost-everywhere exceptional set. -/
theorem spectral_series_of_feature
    (K : Ω → Ω → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (F : Ω → lp (fun _ : ι => ℝ) 2)
    (hcoord : ∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x)
    (hrepresentation : ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫) :
    ∀ᵐ z ∂μ.prod μ, K z.1 z.2 = ∑' i, t i * b i z.1 * b i z.2 := by
  filter_upwards [hrepresentation, Measure.quasiMeasurePreserving_fst.ae hcoord,
    Measure.quasiMeasurePreserving_snd.ae hcoord] with z hz hx hy
  rw [hz]
  exact spectralSign_inner_eq_tsum t (fun i => b i z.1) (fun i => b i z.2)
    (F z.1) (F z.2) hx hy

end Erdos1017.KernelOperator
