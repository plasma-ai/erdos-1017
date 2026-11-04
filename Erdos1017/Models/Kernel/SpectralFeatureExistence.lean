module

public import Erdos1017.Models.Kernel.FeatureKernel
public import Erdos1017.Models.Kernel.SpectralEnergy

/-!
# Existence of a bounded spectral feature

A nonnegative bounded symmetric kernel with only finitely many positive basis
eigenvalues admits a measurable, essentially bounded signed Hilbert feature
representation, via an explicit positive energy bound (`positiveEnergyBound`)
obtained from the bounded eigenfunction equations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

/-- The explicit positive spectral energy bound obtained from the bounded
kernel eigenfunction equations. -/
def positiveEnergyBound {ι : Type*} (B : ℝ) (t : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, ‖t i‖ * (B / t i) ^ 2

theorem positiveEnergyBound_nonneg {ι : Type*} (B : ℝ) (t : ι → ℝ) (s : Finset ι) :
    0 ≤ positiveEnergyBound B t s :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem absolute_energy_bound {ι : Type*} (t a : ι → ℝ) (s : Finset ι)
    (hinside : ∀ i ∈ s, 0 ≤ t i) (houtside : ∀ i ∉ s, t i ≤ 0)
    (D : ℝ) (hpos : (∑ i ∈ s, t i * (a i) ^ 2) ≤ D)
    (hneg : Summable (fun i => max (-t i) 0 * (a i) ^ 2) ∧
      (∑' i, max (-t i) 0 * (a i) ^ 2) ≤ D) :
    Summable (fun i => |t i| * (a i) ^ 2) ∧ (∑' i, |t i| * (a i) ^ 2) ≤ 2 * D := by
  have hpzero : ∀ i ∉ s, max (t i) 0 * (a i) ^ 2 = 0 := by
    intro i hi
    simp [max_eq_right (houtside i hi)]
  have hp : Summable (fun i => max (t i) 0 * (a i) ^ 2) :=
    summable_of_ne_finset_zero hpzero
  have hpsum : (∑' i, max (t i) 0 * (a i) ^ 2) ≤ D := by
    rw [tsum_eq_sum hpzero]
    convert hpos using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [max_eq_left (hinside i hi)]
  have heq : (fun i => |t i| * (a i) ^ 2) =
      (fun i => max (t i) 0 * (a i) ^ 2 + max (-t i) 0 * (a i) ^ 2) := by
    funext i
    by_cases hi : 0 ≤ t i
    · simp [abs_of_nonneg hi, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · have hn := le_of_lt (lt_of_not_ge hi)
      simp [abs_of_nonpos hn, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
  rw [heq]
  exact ⟨hp.add hneg.1, (hp.tsum_add hneg.1).trans_le (by linarith [hneg.2])⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The positive finite spectral part has both a pointwise energy bound and
the corresponding product-almost-everywhere kernel bound. -/
theorem positive_energy_and_kernel_bound
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s : Finset ι) (hpos : ∀ i ∈ s, 0 < t i) :
    (∀ᵐ x ∂μ, (∑ i ∈ s, t i * (b i x) ^ 2) ≤ positiveEnergyBound B t s) ∧
    (∀ᵐ z : Ω × Ω ∂μ.prod μ,
      ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ positiveEnergyBound B t s) := by
  have hb (i : ι) (hi : i ∈ s) : ∀ᵐ x ∂μ, ‖b i x‖ ≤ B / t i := by
    simpa [b.orthonormal.norm_eq_one i, Real.norm_of_nonneg (hpos i hi).le] using
      eigenfunction_bound K hB0 hK hB (b i) (t i) (hpos i hi).ne' (heigen i)
  constructor
  · filter_upwards [s.eventually_all.mpr hb] with x hx
    apply Finset.sum_le_sum
    intro i hi
    have hs : (b i x) ^ 2 ≤ (B / t i) ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hx i hi) 2
    rw [Real.norm_of_nonneg (hpos i hi).le]
    exact mul_le_mul_of_nonneg_left hs (hpos i hi).le
  · exact finiteSpectralKernel_bound b t s (fun i => B / t i) hb

/-- A nonnegative bounded symmetric kernel with only finitely many positive
basis eigenvalues admits a measurable, essentially bounded signed Hilbert
feature representation. The bound is explicit in its positive eigenvalues. -/
theorem exists_bounded_spectral_feature [Countable ι]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s : Finset ι) (hinside : ∀ i ∈ s, 0 < t i)
    (houtside : ∀ i ∉ s, t i ≤ 0) :
    ∃ F : Ω → lp (fun _ : ι => ℝ) 2, AEStronglyMeasurable F μ ∧
      (∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (2 * positiveEnergyBound B t s)) ∧
      (∀ᵐ x ∂μ, ∀ i, F x i = Real.sqrt |t i| * b i x) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫ := by
  have hD := positiveEnergyBound_nonneg B t s
  obtain ⟨hpos, hP⟩ := positive_energy_and_kernel_bound K hB0 hK hB b t heigen s hinside
  have hneg := negative_energy_summable_ae K hB0 hD hK hB hK0 hsym b t heigen
    s (fun i hi => (hinside i hi).le) houtside hP
  have henergy : ∀ᵐ x ∂μ, Summable (fun i => |t i| * (b i x) ^ 2) ∧
      (∑' i, |t i| * (b i x) ^ 2) ≤ 2 * positiveEnergyBound B t s := by
    filter_upwards [hpos, hneg] with x hp hn
    exact absolute_energy_bound t (fun i => b i x) s
      (fun i hi => (hinside i hi).le) houtside _ hp hn
  obtain ⟨F, hF, hcoord, hnorm⟩ := exists_weighted_l2Feature
    (fun i x => b i x) (fun i => (Lp.memLp (b i)).aestronglyMeasurable)
    (fun i => |t i|) (fun i => abs_nonneg _) _ henergy
  have hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (2 * positiveEnergyBound B t s) := by
    filter_upwards [hnorm] with x hx
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hx
  exact ⟨F, hF, hR, hcoord,
    featureKernel_represents K hB0 hK hB b t heigen F hF (Real.sqrt_nonneg _) hR hcoord⟩

end Erdos1017.KernelOperator
