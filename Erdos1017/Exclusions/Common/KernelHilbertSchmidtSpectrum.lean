module

public import Erdos1017.Models.Kernel.KernelCompactness
public import Erdos1017.Models.Kernel.CompactEigenbasis
public import Erdos1017.Exclusions.Common.SpectralSquareVariance

/-!
# Square-summable spectrum of a bounded symmetric kernel

The Hilbert-Schmidt square identity follows from row-wise Parseval and Bessel
bounds without trace class, so a bounded symmetric kernel has a countable
square-summable spectrum with exact total square energy and the sharp
square-weighted variance bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators Classical

namespace Erdos1017.KernelOperator

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The original L² norm is its actual scalar square integral. -/
theorem integral_L2_sq (f : Lp ℝ 2 μ) : (∫ x, (f x) ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [RCLike.inner_apply, conj_trivial, pow_two])

/-- Parseval applied to actual kernel rows gives a common AE all-basis
square-energy identity. No measurable row-map or spectral series is assumed. -/
theorem ae_hasSum_operator_row_energy [Countable ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    ∀ᵐ x ∂μ, HasSum (fun i => (operator K hB0 hK hB (b i) x) ^ 2)
      (∫ y, (K x y) ^ 2 ∂μ) := by
  have hcoeff : ∀ᵐ x ∂μ, ∀ i,
      operator K hB0 hK hB (b i) x = applyKernel (μ := μ) K (b i) x := by
    rw [ae_all_iff]
    intro i
    exact onL2_coe K hK hB (b i)
  filter_upwards [ae_memLp_row hK hB, hcoeff] with x hx hc
  let R := hx.toLp (K x)
  have hn : ‖R‖ ^ 2 = ∫ y, (K x y) ^ 2 ∂μ := by
    rw [← integral_L2_sq]
    apply integral_congr_ae
    filter_upwards [hx.coeFn_toLp] with y hy
    rw [hy]
  have hs : HasSum (fun i => ⟪b i, R⟫ ^ 2) (‖R‖ ^ 2) := by
    convert b.hasSum_inner_mul_inner R R using 1
    · funext i
      rw [real_inner_comm R (b i)]
      ring
    · exact (real_inner_self_eq_norm_sq R).symm
  convert hs using 1
  · funext i
    rw [hc i, applyKernel_eq_inner hx]
  · exact hn.symm

/-- The Hilbert-Schmidt square identity follows from actual row Parseval,
finite Bessel bounds and nonnegative summation. Trace class is not needed. -/
theorem hasSum_operator_basis_energy [Countable ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    HasSum (fun i => ‖operator K hB0 hK hB (b i)‖ ^ 2)
      (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) := by
  let T := operator K hB0 hK hB
  have hrow := ae_hasSum_operator_row_energy K hB0 hK hB b
  have hi (i : ι) : Integrable (fun x => (T (b i) x) ^ 2) μ :=
    (Lp.memLp (T (b i))).integrable_sq
  have hK₂ : Integrable (fun p : Ω × Ω => (K p.1 p.2) ^ 2) (μ.prod μ) :=
    Integrable.of_bound (hK.pow 2) (B ^ 2) (hB.mono (fun p hp => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hp 2))
  have hs : Summable (fun i => ‖T (b i)‖ ^ 2) := by
    apply summable_of_sum_le (fun _ => sq_nonneg _) (c := ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ)
    intro s
    have hfinite : Integrable (fun x => ∑ i ∈ s, (T (b i) x) ^ 2) μ :=
      integrable_finsetSum _ (fun i _ => hi i)
    have hpoint : ∀ᵐ x ∂μ, (∑ i ∈ s, (T (b i) x) ^ 2) ≤ ∫ y, (K x y) ^ 2 ∂μ := by
      filter_upwards [hrow] with x hx
      exact (hx.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)).trans_eq hx.tsum_eq
    have hbessel := integral_mono_ae hfinite hK₂.integral_prod_left hpoint
    rw [← integral_prod _ hK₂, integral_finsetSum _ (fun i _ => hi i)] at hbessel
    simpa only [integral_L2_sq] using hbessel
  have hsumNorm : Summable (fun i => ∫ x, ‖(T (b i) x) ^ 2‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_sq, integral_L2_sq] using hs
  have htsum := integral_tsum_of_summable_integral_norm hi hsumNorm
  have hroweq : (fun x => ∑' i, (T (b i) x) ^ 2) =ᵐ[μ]
      fun x => ∫ y, (K x y) ^ 2 ∂μ := hrow.mono (fun _ hx => hx.tsum_eq)
  have he : (∑' i, ‖T (b i)‖ ^ 2) = ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ := by
    rw [integral_prod _ hK₂, ← integral_congr_ae hroweq]
    simpa only [integral_L2_sq] using htsum
  rw [← he]
  exact hs.hasSum

/-- An actual eigenbasis specializes Hilbert-Schmidt Parseval to the
original square-summable spectrum, with exact total square energy. -/
theorem hasSum_eigenvalues_sq [Countable ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i) :
    HasSum (fun i => (t i) ^ 2) (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) := by
  convert hasSum_operator_basis_energy K hB0 hK hB b using 1
  funext i
  rw [heigen i, norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs, sq_abs]

/-- A genuine bounded symmetric kernel constructs its own countable
square-summable spectrum and the sharp square-weighted variance bound.
No eigenbasis, finite positive rank or trace-class hypothesis is supplied. -/
theorem exists_countable_square_spectrum [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2) (μ.prod μ))
    (hB : ∀ᵐ p ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B)
    (hsym : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = K p.2 p.1) :
    ∃ (κ : Type u) (_ : Countable κ) (b : HilbertBasis κ ℝ (Lp ℝ 2 μ)) (t : κ → ℝ),
      (∀ i, operator K hB0 hK hB (b i) = t i • b i) ∧
      HasSum (fun i => (t i) ^ 2) (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ∧
      Summable (fun i => (t i) ^ 3) ∧ Summable (fun i => (t i) ^ 4) ∧
      (0 < ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ →
        (∑' i, (t i) ^ 4) - (∑' i, (t i) ^ 3) ^ 2 /
            (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ≤
          (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) ^ 2 / 2) := by
  let T := operator K hB0 hK hB
  obtain ⟨κ, hcount, b, t, heigen⟩ := exists_countable_eigen_hilbertBasis T
    (operator_isCompact K hB0 hK hB) (operator_symmetric K hB0 hK hB hsym)
  let : Countable κ := hcount
  have hs := hasSum_eigenvalues_sq K hB0 hK hB b t heigen
  have hbound (i : κ) : |t i| ≤ ‖T‖ := by
    have hi := T.le_opNorm (b i)
    rw [heigen i, norm_smul, b.orthonormal.norm_eq_one, mul_one, mul_one,
      Real.norm_eq_abs] at hi
    exact hi
  obtain ⟨h₃, h₄⟩ := SpectralSquareVariance.summable_cube_fourth t hs.summable ‖T‖ hbound
  refine ⟨κ, hcount, b, t, heigen, hs, h₃, h₄, ?_⟩
  intro hpositive
  have hZ : 0 < ∑' i, (t i) ^ 2 := by rwa [hs.tsum_eq]
  simpa only [hs.tsum_eq] using SpectralSquareVariance.weighted_variance_le_half_square t
    hs.summable hZ

end Erdos1017.KernelOperator
