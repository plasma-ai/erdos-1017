module

public import Erdos1017.Exclusions.Common.CappedConditionalAveraging
public import Erdos1017.Exclusions.Common.ConditionalAveragingRows
public import Erdos1017.Models.Capped.CappedRegularKernel

/-!
# Stationarity survives conditional averaging

A label-constant adjacency is unchanged by the conditional pair average,
averaging commutes with the shifted kernel, and the averaged optimum retains the
row equation of the original multiplier
(`exists_full_conditional_average_stationary`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
  [Countable ι] [DiscreteMeasurableSpace ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A label-constant original adjacency is unchanged by the literal
conditional pair average, on every pair of positive fibers. -/
theorem conditional_average_adjacency (W : Model Ω μ)
    (q : Ω → ι) (hq : Measurable q) (hpos : ∀ i, 0 < μ (q ⁻¹' {i}))
    (H : ι → ι → Bool)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if H (q p.1) (q p.2) = true then 1 else 0) (x y : Ω) :
    ConditionalAveraging.charge (μ := μ) q (adjacencyKernel W) x y =
      if H (q x) (q y) = true then 1 else 0 := by
  let σ := cond μ (q ⁻¹' {q x})
  let τ := cond μ (q ⁻¹' {q y})
  let : IsProbabilityMeasure σ := cond_isProbabilityMeasure (hpos _).ne'
  let : IsProbabilityMeasure τ := cond_isProbabilityMeasure (hpos _).ne'
  have he : ∀ᵐ p ∂σ.prod τ, adjacencyKernel W p.1 p.2 =
      if H (q x) (q y) = true then 1 else 0 := by
    filter_upwards [(cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le hsupport,
      Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hq (measurableSet_singleton (q x)))),
      Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hq (measurableSet_singleton (q y))))]
      with p hp hx hy
    change q p.1 = q x at hx
    change q p.2 = q y at hy
    simpa only [adjacencyKernel, hx, hy] using hp
  change (∫ p, adjacencyKernel W p.1 p.2 ∂σ.prod τ) = _
  rw [integral_congr_ae he]
  simp

omit [MeasurableSpace ι] [Countable ι] [DiscreteMeasurableSpace ι] in
/-- Conditional averaging commutes with the original shifted kernel.
The finite conditional laws license both actual integrals. -/
theorem conditional_average_shifted (W : Model Ω μ) (m : ℝ)
    (q : Ω → ι) (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (x y : Ω) :
    ConditionalAveraging.charge (μ := μ) q (shiftedKernel W m) x y =
      ConditionalAveraging.charge (μ := μ) q (chargeKernel W) x y -
        m * ConditionalAveraging.charge (μ := μ) q (adjacencyKernel W) x y := by
  let σ := (cond μ (q ⁻¹' {q x})).prod (cond μ (q ⁻¹' {q y}))
  let : IsProbabilityMeasure (cond μ (q ⁻¹' {q x})) := cond_isProbabilityMeasure (hpos _).ne'
  let : IsProbabilityMeasure (cond μ (q ⁻¹' {q y})) := cond_isProbabilityMeasure (hpos _).ne'
  have hac : σ ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
  have hY : Integrable (fun p : Ω × Ω => chargeKernel W p.1 p.2) σ :=
    Integrable.of_bound ((chargeKernel_measurable W).mono_ac hac) 3 (hac.ae_le (chargeKernel_bound W))
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) σ :=
    Integrable.of_bound ((adjacencyKernel_measurable W).mono_ac hac) 1 (hac.ae_le (adjacencyKernel_bound W))
  change (∫ p, shiftedKernel W m p.1 p.2 ∂σ) =
    (∫ p, chargeKernel W p.1 p.2 ∂σ) - m * ∫ p, adjacencyKernel W p.1 p.2 ∂σ
  simp_rw [shiftedKernel, shiftedMoment_eq]
  exact (integral_sub hY (hG.const_mul m)).trans (by rw [integral_const_mul])

/-- The actual averaged optimum retains its original multiplier's row
equation. This is proved by averaging the original shifted row, without
assigning a new optimizer's selected multiplier or selected structure. -/
theorem exists_full_conditional_average_stationary
    (W : Model Ω μ) (hW : FullFeasible W) (m ν : ℝ)
    (hstationary : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (q : Ω → ι) (hq : Measurable q) (hpos : ∀ i, 0 < μ (q ⁻¹' {i}))
    (H : ι → ι → Bool) (hHsym : ∀ i j, H i j = H j i)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if H (q p.1) (q p.2) = true then 1 else 0) :
    ∃ V : Model Ω μ, FullFeasible V ∧ density V = density W ∧ objective V = objective W ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p = (if H (q p.1) (q p.2) = true then 1 else 0) ∧
        V.moment CappedColor.charge p =
          ConditionalAveraging.charge (μ := μ) q (chargeKernel W) p.1 p.2) ∧
      ∀ x, (∫ y, shiftedKernel V m x y ∂μ) = ν := by
  obtain ⟨V, hfull, hd, hc, hmom⟩ :=
    exists_full_conditional_average W hW q hq hpos H hHsym hsupport
  refine ⟨V, hfull, hd, hc, hmom, ?_⟩
  have hM : Measurable (Function.uncurry (shiftedKernel W m)) :=
    (W.stronglyMeasurable_moment (continuous_shiftedColor m).measurable.stronglyMeasurable).measurable
  have hbound (x y : Ω) : ‖shiftedKernel W m x y‖ ≤ 3 + ‖m‖ := by
    have h := norm_integral_le_of_norm_le_const (μ := W.kernel (x, y))
      (Eventually.of_forall (shiftedColor_norm_le m))
    simpa only [shiftedKernel, shiftedMoment, DecoratedKernel.moment, probReal_univ, mul_one] using h
  have hrow (x : Ω) := ConditionalAveraging.integral_charge_row_eq q hq hpos
    (shiftedKernel W m) hM (3 + ‖m‖) hbound (fun _ => ν) hstationary x
  intro x
  calc
    _ = ∫ y, ConditionalAveraging.charge (μ := μ) q (shiftedKernel W m) x y ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        rw [conditional_average_shifted W m q hpos x y,
          conditional_average_adjacency W q hq hpos H hsupport x y]
        change shiftedMoment V m (x, y) = _
        rw [shiftedMoment_eq, (hmom (x, y)).1, (hmom (x, y)).2])
    _ = ν := hrow x

end Erdos1017.CappedModel
