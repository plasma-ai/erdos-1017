module

public import Erdos1017.Models.Capped.CappedKernelConvergence
public import Erdos1017.Models.Decorated.DecoratedCappedCompactness
public import Erdos1017.Models.Kernel.KernelReindexing
public import Erdos1017.Models.Kernel.KernelPositiveIndexStability

/-!
# Shifted-color intervals and rows in the limit

Moving the multiplier changes a shifted color by at most the multiplier
displacement, constant rows and the positive index bound pass to an operator
norm limit, and the nonnegative selected shifted-color interval passes to the
same joint-law limit even though the multipliers vary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The continuous violation of the selected shifted-color interval. -/
def shiftedIntervalViolation (m : ℝ) : C(CappedColor, ℝ) :=
  ⟨fun c => max (-shiftedColor m c) 0 + max (shiftedColor m c - 4) 0,
    ((continuous_shiftedColor m).neg.max continuous_const).add
      (((continuous_shiftedColor m).sub continuous_const).max continuous_const)⟩

theorem shiftedIntervalViolation_nonneg (m : ℝ) (c : CappedColor) :
    0 ≤ shiftedIntervalViolation m c :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem shiftedIntervalViolation_eq_zero (m : ℝ) (c : CappedColor) :
    shiftedIntervalViolation m c = 0 ↔ shiftedColor m c ∈ Set.Icc 0 4 := by
  change max (-shiftedColor m c) 0 + max (shiftedColor m c - 4) 0 = 0 ↔ _
  constructor
  · intro h
    have h₁ := le_max_left (-shiftedColor m c) 0
    have h₂ := le_max_left (shiftedColor m c - 4) 0
    have h₃ := le_max_right (-shiftedColor m c) 0
    have h₄ := le_max_right (shiftedColor m c - 4) 0
    constructor <;> linarith
  · intro h
    rw [max_eq_right (by linarith [h.1]), max_eq_right (by linarith [h.2])]
    norm_num

/-- Moving the actual multiplier changes a shifted color by at most the
multiplier displacement, since sampled adjacency lies in the unit interval. -/
theorem shiftedColor_sub_abs_le (m m' : ℝ) (c : CappedColor) :
    |shiftedColor m c - shiftedColor m' c| ≤ |m - m'| := by
  have heq : shiftedColor m c - shiftedColor m' c =
      -(m - m') * CappedColor.adjacency c := by
    unfold shiftedColor
    ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg (CappedColor.adjacency_mem c).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (CappedColor.adjacency_mem c).2

theorem shiftedIntervalViolation_le (m m' : ℝ) (c : CappedColor)
    (hc : shiftedColor m' c ∈ Set.Icc 0 4) :
    shiftedIntervalViolation m c ≤ 2 * |m - m'| := by
  have h := abs_le.mp (shiftedColor_sub_abs_le m m' c)
  change max (-shiftedColor m c) 0 + max (shiftedColor m c - 4) 0 ≤ _
  have h₁ : max (-shiftedColor m c) 0 ≤ |m - m'| :=
    max_le (by linarith [hc.1]) (abs_nonneg _)
  have h₂ : max (shiftedColor m c - 4) 0 ≤ |m - m'| :=
    max_le (by linarith [hc.2]) (abs_nonneg _)
  linarith

omit [IsProbabilityMeasure μ] in
/-- Actual conditional color support bounds the actual conditional mean. -/
theorem shiftedMoment_mem_of_color_mem (W : Model Ω μ) (m : ℝ)
    (hcolor : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c ∈ Set.Icc 0 4) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Set.Icc 0 4 := by
  filter_upwards [hcolor] with p hp
  have hi : Integrable (shiftedColor m) (W.kernel p) :=
    Integrable.of_bound (continuous_shiftedColor m).aestronglyMeasurable (3 + ‖m‖)
      (Eventually.of_forall (shiftedColor_norm_le m))
  constructor
  · exact integral_nonneg_of_ae (hp.mono fun _ hc => hc.1)
  · change (∫ c, shiftedColor m c ∂W.kernel p) ≤ 4
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae hi (integrable_const (4 : ℝ)) (hp.mono fun _ hc => hc.2)

/-- Constant actual rows pass to an actual operator norm limit, with the
stationary scalar converging along that same sequence. -/
theorem shifted_row_of_operator_limit (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (m : ℕ → ℝ) (m₀ : ℝ) (ν : ℕ → ℝ) (ν₀ : ℝ)
    (hop : Tendsto (fun n => shiftedOperator (W n) (m n)) atTop (𝓝 (shiftedOperator V m₀)))
    (hν : Tendsto ν atTop (𝓝 ν₀))
    (hrow : ∀ n, ∀ᵐ x ∂μ, (∫ y, shiftedKernel (W n) (m n) x y ∂μ) = ν n) :
    ∀ᵐ x ∂μ, (∫ y, shiftedKernel V m₀ x y ∂μ) = ν₀ := by
  let u := Lp.const 2 μ (1 : ℝ)
  have heigen (n : ℕ) : shiftedOperator (W n) (m n) u = ν n • u :=
    KernelOperator.constant_one_eigenvector_of_stationary _ (by positivity)
      (shiftedKernel_measurable (W n) (m n)) (shiftedKernel_bound (W n) (m n)) (ν n) (hrow n)
  have hleft : Tendsto (fun n => shiftedOperator (W n) (m n) u) atTop
      (𝓝 (shiftedOperator V m₀ u)) :=
    (show Continuous (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T u) by fun_prop).continuousAt.tendsto.comp hop
  have hright : Tendsto (fun n => ν n • u) atTop (𝓝 (ν₀ • u)) := hν.smul_const u
  have hlim : shiftedOperator V m₀ u = ν₀ • u :=
    tendsto_nhds_unique hleft (by simpa only [heigen] using hright)
  exact KernelOperator.stationary_of_constant_one_eigenvector _ (by positivity)
    (shiftedKernel_measurable V m₀) (shiftedKernel_bound V m₀) ν₀ hlim

/-- The positive index of the actual shifted operator is at most the
sequence bound; no aligned or limit index premise is inserted. -/
theorem positive_shifted_index_of_operator_limit [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (m : ℕ → ℝ) (m₀ : ℝ)
    (hop : Tendsto (fun n => shiftedOperator (W n) (m n)) atTop (𝓝 (shiftedOperator V m₀)))
    (hfinite : ∀ n, FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W n) (m n))))
    (r : ℕ) (hindex : ∀ n, Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (W n) (m n))) ≤ r) :
    FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ≤ r := by
  apply KernelOperator.positive_index_le_of_tendsto hop _ _ hfinite r hindex
  · intro n
    exact KernelOperator.operator_isCompact _ (by positivity)
      (shiftedKernel_measurable (W n) (m n)) (shiftedKernel_bound (W n) (m n))
  · intro n
    exact KernelOperator.operator_symmetric _ (by positivity)
      (shiftedKernel_measurable (W n) (m n)) (shiftedKernel_bound (W n) (m n))
      ((shiftedMoment_symm (W n) (m n)).mono fun _ hp => hp.symm)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The nonnegative selected shifted-color interval passes to the same
joint-law limit, even though its actual multipliers vary along the sequence. -/
theorem shiftedColor_mem_of_jointLaw_limit (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (m : ℕ → ℝ) (m₀ : ℝ)
    (hweak : Tendsto (fun n => (W n).jointLaw) atTop (𝓝 V.jointLaw))
    (hm : Tendsto m atTop (𝓝 m₀))
    (hcolor : ∀ n, ∀ᵐ p ∂μ.prod μ,
      ∀ᵐ c ∂(W n).kernel p, shiftedColor (m n) c ∈ Set.Icc 0 4) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂V.kernel p, shiftedColor m₀ c ∈ Set.Icc 0 4 := by
  let f := shiftedIntervalViolation m₀
  have hi (X : Model Ω μ) : Integrable (X.moment f) (μ.prod μ) :=
    integrable_bounded_moment X f f.continuous.stronglyMeasurable ‖f‖ f.norm_coe_le_norm
  have hn (X : Model Ω μ) (p : Ω × Ω) : 0 ≤ X.moment f p :=
    integral_nonneg (shiftedIntervalViolation_nonneg m₀)
  have hbound (n : ℕ) : (∫ p, (W n).moment f p ∂μ.prod μ) ≤ 2 * |m₀ - m n| := by
    have hp : ∀ᵐ p ∂μ.prod μ, (W n).moment f p ≤ 2 * |m₀ - m n| := by
      filter_upwards [hcolor n] with p hp
      have hif : Integrable f ((W n).kernel p) :=
        Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
          (Eventually.of_forall f.norm_coe_le_norm)
      change (∫ c, f c ∂(W n).kernel p) ≤ _
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono_ae hif (integrable_const (2 * |m₀ - m n|))
          (hp.mono fun c hc => shiftedIntervalViolation_le m₀ (m n) c hc)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae (hi (W n)) (integrable_const (2 * |m₀ - m n|)) hp
  have hzlim : Tendsto (fun n => ∫ p, (W n).moment f p ∂μ.prod μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (hn (W n))) hbound
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ => m₀) atTop (𝓝 m₀)).sub hm).abs.const_mul 2)
  have hz : (∫ p, V.moment f p ∂μ.prod μ) = 0 :=
    tendsto_nhds_unique (DecoratedKernel.integral_moment_tendsto_of_jointLaw W V hweak f) hzlim
  have hpzero := (integral_eq_zero_iff_of_nonneg (hn V) (hi V)).mp hz
  filter_upwards [hpzero] with p hp
  have hif : Integrable f (V.kernel p) :=
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall f.norm_coe_le_norm)
  have hc := (integral_eq_zero_iff_of_nonneg (shiftedIntervalViolation_nonneg m₀) hif).mp hp
  exact hc.mono (fun c hc => (shiftedIntervalViolation_eq_zero m₀ c).mp hc)

end Erdos1017.CappedModel
