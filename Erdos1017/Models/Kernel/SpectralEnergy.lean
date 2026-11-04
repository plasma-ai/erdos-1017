module

public import Erdos1017.Models.Kernel.KernelSpectralPart
public import Erdos1017.Models.PhysicalPrimal.FiniteEnergyBound

/-!
# Bounds on negative spectral energy

Every finite portion of the negative spectral energy is bounded by the full
positive energy minus the operator quadratic form, and positivity of the kernel
bounds finite negative cell energies, giving summable negative spectral energy
with a uniform essential bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

/-- Every finite portion of the negative spectral energy is bounded by the
full positive energy minus the operator quadratic form. -/
theorem negative_partial_quadratic_bound {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis ι ℝ E) (T : E →L[ℝ] E)
    (hs : T.toLinearMap.IsSymmetric) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (s j : Finset ι)
    (houtside : ∀ i ∉ s, t i ≤ 0) (hdisj : Disjoint s j) (x : E) :
    (∑ i ∈ j, -t i * ⟪b i, x⟫ ^ 2) ≤
      (∑ i ∈ s, t i * ⟪b i, x⟫ ^ 2) - ⟪T x, x⟫ := by
  classical
  let p : ι → ℝ := fun i => if i ∈ s then t i * ⟪b i, x⟫ ^ 2 else 0
  let q : ι → ℝ := fun i => p i - t i * ⟪b i, x⟫ ^ 2
  have hpzero : ∀ i ∉ s, p i = 0 := fun i hi => by simp [p, hi]
  have hp : Summable p := summable_of_ne_finset_zero hpzero
  have hspec := hasSum_eigen_quadratic b T hs t heigen x
  have hq : Summable q := hp.sub hspec.summable
  have hqnonneg (i : ι) : 0 ≤ q i := by
    by_cases hi : i ∈ s
    · simp [q, p, hi]
    · simpa [q, p, hi] using neg_nonneg.mpr
        (mul_nonpos_of_nonpos_of_nonneg (houtside i hi) (sq_nonneg _))
  have hsum := hq.sum_le_tsum j (fun i _ => hqnonneg i)
  have hj : (∑ i ∈ j, q i) = ∑ i ∈ j, -t i * ⟪b i, x⟫ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hn : i ∉ s := fun his => Finset.disjoint_left.mp hdisj his hi
    simp [q, p, hn]
  have htotal : (∑' i, q i) = (∑ i ∈ s, t i * ⟪b i, x⟫ ^ 2) - ⟪T x, x⟫ := by
    rw [show q = (fun i => p i - t i * ⟪b i, x⟫ ^ 2) from rfl,
      hp.tsum_sub hspec.summable, hspec.tsum_eq, tsum_eq_sum hpzero]
    simp [p]
  rwa [hj, htotal] at hsum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem indicator_quadratic_le (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (s : Set Ω) (hs : MeasurableSet s) :
    ⟪operator K hB0 hK hB (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)),
      indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)⟫ ≤ B * (μ.real s) ^ 2 := by
  rw [indicator_quadratic_eq]
  have hi : Integrable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ) :=
    (show MemLp (fun z : Ω × Ω => K z.1 z.2) 1 (μ.prod μ) from
      MemLp.of_bound hK B hB).integrable le_rfl
  have hle : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 ≤ B :=
    hB.mono (fun z hz => (le_abs_self _).trans hz)
  have hh := setIntegral_mono_ae (s := s ×ˢ s) hi.integrableOn
    (integrable_const B).integrableOn hle
  refine hh.trans_eq ?_
  rw [setIntegral_const]
  simp [measureReal_def, Measure.prod_prod, smul_eq_mul, pow_two, mul_comm]

/-- Positivity of the original kernel bounds every finite negative spectral
cell energy by the uniform bound on its finite positive spectral kernel. -/
theorem negative_partial_cell_energy_le {ι : Type*}
    (K : Ω → Ω → ℝ) {B D : ℝ} (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s j : Finset ι) (houtside : ∀ i ∉ s, t i ≤ 0) (hdisj : Disjoint s j)
    (hP : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ D)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∑ i ∈ j, -t i * (∫ x in A, b i x ∂μ) ^ 2) ≤ D * (μ.real A) ^ 2 := by
  let u := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  have hi (i : ι) : ⟪b i, u⟫ = ∫ x in A, b i x ∂μ := by
    rw [real_inner_comm]
    exact L2.inner_indicatorConstLp_one hA (measure_ne_top μ A) (b i)
  have hn : 0 ≤ ⟪operator K hB0 hK hB u, u⟫ := by
    rw [show u = indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) from rfl,
      indicator_quadratic_eq]
    exact integral_nonneg_of_ae (ae_restrict_of_ae hK0)
  have hneg := negative_partial_quadratic_bound b (operator K hB0 hK hB)
    (operator_symmetric K hB0 hK hB hsym) t heigen s j houtside hdisj u
  simp_rw [hi] at hneg
  have hpositive : (∑ i ∈ s, t i * (∫ x in A, b i x ∂μ) ^ 2) ≤ D * (μ.real A) ^ 2 := by
    have h := indicator_quadratic_le (finiteSpectralKernel (μ := μ) b t s) hD0
      (finiteSpectralKernel_measurable b t s) hP A hA
    rw [operator_finiteSpectralKernel, finiteSpectralOperator_quadratic] at h
    simpa only [← hi] using h
  linarith

/-- Every finite negative spectral energy is essentially bounded by the
positive-kernel bound. This derives the pointwise estimate directly from
cell integrals, without an infinite-dimensional trace axiom. -/
theorem negative_partial_energy_ae_le {ι : Type*}
    (K : Ω → Ω → ℝ) {B D : ℝ} (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s j : Finset ι) (houtside : ∀ i ∉ s, t i ≤ 0) (hdisj : Disjoint s j)
    (hP : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ D) :
    ∀ᵐ x ∂μ, (∑ i ∈ j, -t i * (b i x) ^ 2) ≤ D := by
  classical
  have hweight (i : j) : 0 ≤ -t i := by
    apply neg_nonneg.mpr
    exact houtside i (fun hi => Finset.disjoint_left.mp hdisj hi i.property)
  have h := ae_weighted_sum_sq_le_of_setIntegral_sum_sq_le
    (fun i : j => (b i : Ω → ℝ))
    (fun i => (Lp.memLp (b i)).integrable (by norm_num))
    (fun i : j => -t i) hweight D hD0 (by
      intro A hA
      rw [Finset.sum_coe_sort j (fun i => -t i * (∫ x in A, b i x ∂μ) ^ 2)]
      exact negative_partial_cell_energy_le K hB0 hD0 hK hB hK0 hsym b t heigen s j houtside hdisj hP A hA)
  filter_upwards [h] with x hx
  rwa [Finset.sum_coe_sort j (fun i => -t i * (b i x) ^ 2)] at hx

/-- Countably many finite-energy bounds yield summable negative spectral
energy and its uniform essential bound. -/
theorem negative_energy_summable_ae {ι : Type*} [Countable ι]
    (K : Ω → Ω → ℝ) {B D : ℝ} (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (t : ι → ℝ)
    (heigen : ∀ i, operator K hB0 hK hB (b i) = t i • b i)
    (s : Finset ι) (hinside : ∀ i ∈ s, 0 ≤ t i) (houtside : ∀ i ∉ s, t i ≤ 0)
    (hP : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖finiteSpectralKernel (μ := μ) b t s z.1 z.2‖ ≤ D) :
    ∀ᵐ x ∂μ, Summable (fun i => max (-t i) 0 * (b i x) ^ 2) ∧
      (∑' i, max (-t i) 0 * (b i x) ^ 2) ≤ D := by
  classical
  have hfinite (j : Finset ι) :
      ∀ᵐ x ∂μ, (∑ i ∈ j, max (-t i) 0 * (b i x) ^ 2) ≤ D := by
    have hd : Disjoint s (j.filter (fun i => i ∉ s)) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_filter.mp hj).2 hi
    filter_upwards [negative_partial_energy_ae_le K hB0 hD0 hK hB hK0 hsym b t heigen
      s (j.filter (fun i => i ∉ s)) houtside hd hP] with x hx
    have heq : (∑ i ∈ j, max (-t i) 0 * (b i x) ^ 2) =
        ∑ i ∈ j.filter (fun i => i ∉ s), -t i * (b i x) ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp [hi, max_eq_right (neg_nonpos.mpr (hinside i hi))]
      · simp [hi, max_eq_left (neg_nonneg.mpr (houtside i hi))]
    rwa [heq]
  have hall : ∀ᵐ x ∂μ, ∀ j : Finset ι,
      (∑ i ∈ j, max (-t i) 0 * (b i x) ^ 2) ≤ D := ae_all_iff.mpr hfinite
  filter_upwards [hall] with x hx
  have hn (i : ι) : 0 ≤ max (-t i) 0 * (b i x) ^ 2 :=
    mul_nonneg (le_max_right _ _) (sq_nonneg _)
  exact ⟨summable_of_sum_le hn hx, Real.tsum_le_of_sum_le hn hx⟩

end Erdos1017.KernelOperator
