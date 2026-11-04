module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Tactic.Linarith

/-!
# Conditional barycenters near feature support points

This module defines `featureBallDensity`, the normalized density of a
feature-ball preimage, which is bounded, integrable and of mean one, and shows
that its Bochner barycenter is the conditional set average, lies within the ball
radius of the support point, and converges to every feature-law support point as
the ball shrinks.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace Erdos1017.KernelOperator

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The actual normalized density of a feature-ball preimage. -/
def featureBallDensity (F : Ω → E) (a : E) (ε : ℝ) : Ω → ℝ :=
  (F ⁻¹' ball a ε).indicator (fun _ => (μ.real (F ⁻¹' ball a ε))⁻¹)

omit [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure μ] in
/-- Every neighborhood of an actual feature-law support point has
positive physical preimage mass. -/
theorem feature_ball_preimage_pos (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ha : a ∈ (μ.map F).support) (ε : ℝ) (hε : 0 < ε) :
    0 < μ (F ⁻¹' ball a ε) := by
  have hp := (Measure.mem_support_iff_forall a).mp ha (ball a ε) (ball_mem_nhds a hε)
  rwa [Measure.map_apply hF.measurable isOpen_ball.measurableSet] at hp

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Each conditional density is an actual bounded integrable function;
the bound can depend on the positive ball mass. -/
theorem featureBallDensity_integrable (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ε : ℝ) : Integrable (featureBallDensity (μ := μ) F a ε) μ :=
  (integrable_const _).indicator (hF.measurable isOpen_ball.measurableSet)

omit [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [IsFiniteMeasure μ] in
/-- Positivity and a finite pointwise bound hold for the displayed density. -/
theorem featureBallDensity_bounds (F : Ω → E) (a : E) (ε : ℝ) (x : Ω) :
    0 ≤ featureBallDensity (μ := μ) F a ε x ∧
      ‖featureBallDensity (μ := μ) F a ε x‖ ≤ (μ.real (F ⁻¹' ball a ε))⁻¹ := by
  have hp : 0 ≤ (μ.real (F ⁻¹' ball a ε))⁻¹ := inv_nonneg.mpr measureReal_nonneg
  by_cases hx : x ∈ F ⁻¹' ball a ε
  · simp only [featureBallDensity, indicator_of_mem hx, Real.norm_of_nonneg hp, le_refl, and_true]
    exact hp
  · simp only [featureBallDensity, indicator_of_notMem hx, le_refl, norm_zero, true_and]
    exact hp

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Normalization gives mean one under the original physical measure. -/
theorem featureBallDensity_integral (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ha : a ∈ (μ.map F).support) (ε : ℝ) (hε : 0 < ε) :
    (∫ x, featureBallDensity (μ := μ) F a ε x ∂μ) = 1 := by
  have hp := feature_ball_preimage_pos F hF a ha ε hε
  have hm : μ.real (F ⁻¹' ball a ε) ≠ 0 :=
    (ENNReal.toReal_pos hp.ne' (measure_ne_top μ _)).ne'
  rw [featureBallDensity, integral_indicator (hF.measurable isOpen_ball.measurableSet), setIntegral_const]
  simp only [smul_eq_mul, mul_inv_cancel₀ hm]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The feature is integrable on a small-ball preimage even without a
global bound or a global integrability assumption. -/
theorem feature_integrableOn_ball (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ε : ℝ) : IntegrableOn F (F ⁻¹' ball a ε) μ := by
  apply Integrable.of_bound hF.aestronglyMeasurable (‖a‖ + ε)
  filter_upwards [ae_restrict_mem (hF.measurable isOpen_ball.measurableSet)] with x hx
  have hd : ‖F x - a‖ < ε := by simpa only [mem_preimage, mem_ball, dist_eq_norm] using hx
  have hn := norm_add_le (F x - a) a
  rw [sub_add_cancel] at hn
  linarith

omit [CompleteSpace E] in
/-- The density-weighted feature is Bochner integrable under the original
measure, with no global bound on F required. -/
theorem featureBallDensity_smul_integrable (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ε : ℝ) :
    Integrable (fun x => featureBallDensity (μ := μ) F a ε x • F x) μ := by
  have heq : (fun x => featureBallDensity (μ := μ) F a ε x • F x) =
      (F ⁻¹' ball a ε).indicator (fun x => (μ.real (F ⁻¹' ball a ε))⁻¹ • F x) := by
    funext x
    by_cases hx : x ∈ F ⁻¹' ball a ε <;> simp [featureBallDensity, hx]
  rw [heq, integrable_indicator_iff (hF.measurable isOpen_ball.measurableSet)]
  exact (feature_integrableOn_ball F hF a ε).smul _

omit [CompleteSpace E] [IsFiniteMeasure μ] in
/-- The Bochner barycenter of the actual normalized density is precisely
the conditional set average, not an average of pointwise quadratic values. -/
theorem featureBallDensity_barycenter (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ε : ℝ) :
    (∫ x, featureBallDensity (μ := μ) F a ε x • F x ∂μ) =
      ⨍ x in F ⁻¹' ball a ε, F x ∂μ := by
  rw [setAverage_eq]
  have heq : (fun x => featureBallDensity (μ := μ) F a ε x • F x) =
      (F ⁻¹' ball a ε).indicator (fun x => (μ.real (F ⁻¹' ball a ε))⁻¹ • F x) := by
    funext x
    by_cases hx : x ∈ F ⁻¹' ball a ε <;> simp [featureBallDensity, hx]
  rw [heq, integral_indicator (hF.measurable isOpen_ball.measurableSet), integral_smul]

/-- The constructed conditional barycenter stays within the feature-ball
radius of the support point. Convexity is applied to the barycenter itself. -/
theorem featureBallDensity_barycenter_dist_le (F : Ω → E) (hF : StronglyMeasurable F)
    (a : E) (ha : a ∈ (μ.map F).support) (ε : ℝ) (hε : 0 < ε) :
    dist (∫ x, featureBallDensity (μ := μ) F a ε x • F x ∂μ) a ≤ ε := by
  rw [featureBallDensity_barycenter F hF a ε]
  apply (convex_closedBall a ε).set_average_mem isClosed_closedBall
    (feature_ball_preimage_pos F hF a ha ε hε).ne' (measure_ne_top μ _)
      _ (feature_integrableOn_ball F hF a ε)
  filter_upwards [ae_restrict_mem (hF.measurable isOpen_ball.measurableSet)] with x hx
  exact ball_subset_closedBall hx

/-- Arbitrarily shrinking positive feature balls give actual normalized
conditional barycenters converging to every feature-law support point. -/
theorem featureBallDensity_barycenter_tendsto
    (F : Ω → E) (hF : StronglyMeasurable F) (a : E) (ha : a ∈ (μ.map F).support)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => ∫ x, featureBallDensity (μ := μ) F a (ε i) x • F x ∂μ) l (𝓝 a) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun i => featureBallDensity_barycenter_dist_le F hF a ha (ε i) (hε i)) hlim

end Erdos1017.KernelOperator
