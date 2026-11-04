module

public import Erdos1017.Models.Kernel.PositiveSpectralSubspace

/-!
# Uniform bounds on spectral features

A uniform bound on the positive spectral energy bounds the complete signed
feature map independently of the number of negative eigenvalues, and a constant
positive direction plus one further positive eigenvalue bounded below by `s₀`
gives the explicit feature norm bound used in finite-order stabilization.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finiteSpectralKernel_bound_of_energy
    (b : ι → Lp ℝ 2 μ) (t : ι → ℝ) (s : Finset ι) (ht : ∀ i ∈ s, 0 ≤ t i)
    {D : ℝ} (hD : 0 ≤ D)
    (henergy : ∀ᵐ x ∂μ, (∑ i ∈ s, t i * (b i x) ^ 2) ≤ D) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ D := by
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae henergy,
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae henergy] with z hx hy
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => t i * (b i z.1) ^ 2) (g := fun i => t i * (b i z.2) ^ 2)
    (r := fun i => t i * b i z.1 * b i z.2)
    (fun i hi => mul_nonneg (ht i hi) (sq_nonneg _))
    (fun i hi => mul_nonneg (ht i hi) (sq_nonneg _)) (fun i _ => by ring_nf; rfl)
  have hm : (∑ i ∈ s, t i * (b i z.1) ^ 2) * (∑ i ∈ s, t i * (b i z.2) ^ 2) ≤ D ^ 2 := by
    exact (mul_le_mul hx hy (Finset.sum_nonneg (fun i hi => mul_nonneg (ht i hi)
      (sq_nonneg _))) hD).trans_eq (by ring)
  have hsq : ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ^ 2 ≤ D ^ 2 := by
    simpa only [finiteSpectralKernel, Real.norm_eq_abs, sq_abs] using hs.trans hm
  exact (sq_le_sq₀ (norm_nonneg _) hD).mp hsq

/-- A uniform bound on the positive spectral energy gives a uniform bound
on the complete signed feature map, independently of the number of negative
eigenvalues. -/
theorem exists_bounded_spectral_feature_of_energy [Countable ι]
    (K : Ω → Ω → ℝ) {B D : ℝ} (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s : Finset ι) (hinside : ∀ i ∈ s, 0 ≤ t i) (houtside : ∀ i ∉ s, t i ≤ 0)
    (hpos : ∀ᵐ x ∂μ, (∑ i ∈ s, t i * (b i x) ^ 2) ≤ D) :
    ∃ F : Ω → lp (fun _ : ι => ℝ) 2, AEStronglyMeasurable F μ ∧
      (∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (2 * D)) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫ := by
  have hP := finiteSpectralKernel_bound_of_energy (μ := μ) b t s hinside hD0 hpos
  have hneg := negative_energy_summable_ae K hB0 hD0 hK hB hK0 hsym b t heigen
    s hinside houtside hP
  have henergy : ∀ᵐ x ∂μ, Summable (fun i => |t i| * (b i x) ^ 2) ∧
      (∑' i, |t i| * (b i x) ^ 2) ≤ 2 * D := by
    filter_upwards [hpos, hneg] with x hp hn
    exact absolute_energy_bound t (fun i => b i x) s hinside houtside D hp hn
  obtain ⟨F, hF, hcoord, hnorm⟩ := exists_weighted_l2Feature
    (fun i x => b i x) (fun i => (Lp.memLp (b i)).aestronglyMeasurable)
    (fun i => |t i|) (fun i => abs_nonneg _) _ henergy
  have hR : ∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (2 * D) := by
    filter_upwards [hnorm] with x hx
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hx
  exact ⟨F, hF, hR,
    featureKernel_represents K hB0 hK hB b t heigen F hF (Real.sqrt_nonneg _) hR hcoord⟩

/-- The explicit bound used in finite-order stabilization: a constant
positive direction and one further positive eigenvalue bounded below by
`s₀` yield feature norm squared at most `8 + 32 / s₀`. -/
theorem exists_bounded_two_positive_feature [Countable ι]
    (K : Ω → Ω → ℝ)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ 4)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K (by norm_num) hK hB (b i) = t i • b i)
    (i₀ i₁ : ι) (hne : i₀ ≠ i₁) (hconstant : ∀ᵐ x ∂μ, b i₀ x = 1)
    (ht₀ : 0 ≤ t i₀ ∧ t i₀ ≤ 4) {s₀ : ℝ} (hs₀ : 0 < s₀) (ht₁ : s₀ ≤ t i₁)
    (houtside : ∀ i, i ≠ i₀ → i ≠ i₁ → t i ≤ 0) :
    ∃ F : Ω → lp (fun _ : ι => ℝ) 2, AEStronglyMeasurable F μ ∧
      (∀ᵐ x ∂μ, ‖F x‖ ≤ Real.sqrt (8 + 32 / s₀)) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ⟪spectralSign t (F z.1), F z.2⟫ := by
  classical
  have ht : 0 < t i₁ := hs₀.trans_le ht₁
  have hb : ∀ᵐ x ∂μ, ‖b i₁ x‖ ≤ 4 / t i₁ := by
    simpa [b.orthonormal.norm_eq_one i₁, Real.norm_of_nonneg ht.le] using
      eigenfunction_bound K (by norm_num) hK hB (b i₁) (t i₁) ht.ne' (heigen i₁)
  have hpos : ∀ᵐ x ∂μ, (∑ i ∈ ({i₀, i₁} : Finset ι), t i * (b i x) ^ 2) ≤
      4 + 16 / s₀ := by
    filter_upwards [hconstant, hb] with x hc hx
    have hs : (b i₁ x) ^ 2 ≤ (4 / t i₁) ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hv : t i₁ * (b i₁ x) ^ 2 ≤ 16 / s₀ := calc
      _ ≤ t i₁ * (4 / t i₁) ^ 2 := mul_le_mul_of_nonneg_left hs ht.le
      _ = 16 / t i₁ := by field_simp; ring
      _ ≤ 16 / s₀ := div_le_div_of_nonneg_left (by norm_num) hs₀ ht₁
    simp only [Finset.sum_pair hne, hc, one_pow, mul_one]
    linarith [ht₀.2]
  have hinside : ∀ i ∈ ({i₀, i₁} : Finset ι), 0 ≤ t i := by
    intro i hi
    rcases (show i = i₀ ∨ i = i₁ by simpa only [Finset.mem_insert, Finset.mem_singleton] using hi) with rfl | rfl
    · exact ht₀.1
    · exact ht.le
  have hout : ∀ i ∉ ({i₀, i₁} : Finset ι), t i ≤ 0 := by
    intro i hi
    exact houtside i (fun h => hi (by simp [h])) (fun h => hi (by simp [h]))
  have heq : 2 * (4 + 16 / s₀) = 8 + 32 / s₀ := by ring
  simpa only [heq] using exists_bounded_spectral_feature_of_energy K (by norm_num)
    (by positivity : 0 ≤ 4 + 16 / s₀) hK hB hK0 hsym b t heigen
    {i₀, i₁} hinside hout hpos

end Erdos1017.KernelOperator
