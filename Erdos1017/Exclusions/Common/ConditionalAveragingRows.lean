module

public import Erdos1017.Exclusions.Common.CountableConditionalAveraging

/-!
# Row integrals under conditional averaging

Conditioning on the positive fibers preserves a scalar integral, the row of the
pair average is the conditional average of the original row, and a row equation
whose right side is constant on each fiber survives the full conditional
averaging.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.ConditionalAveraging

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
  [Countable ι] [DiscreteMeasurableSpace ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Conditioning on the actual positive fibers preserves a scalar
integral. The conditional expectation is identified internally. -/
theorem integral_fiber_average (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ x, (∫ y, f y ∂cond μ (q ⁻¹' {q x})) ∂μ) = ∫ x, f x ∂μ := by
  have he (x : Ω) := PhysicalPartitionAverages.fiberAverage_eq_condExp
    μ q hq hf x (hpos _).ne'
  simp only [setAverage_eq'] at he
  change ∀ x, (∫ y, f y ∂cond μ (q ⁻¹' {q x})) = _ at he
  rw [integral_congr_ae (Eventually.of_forall he)]
  exact integral_condExp hq.comap_le

/-- The row of the actual pair average is the conditional average of
the original row. Both integrations use the original probability law. -/
theorem integral_charge_row (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B) (x : Ω) :
    (∫ y, charge (μ := μ) q Y x y ∂μ) =
      ∫ z, (∫ y, Y z y ∂μ) ∂cond μ (q ⁻¹' {q x}) := by
  let σ := cond μ (q ⁻¹' {q x})
  let : IsProbabilityMeasure σ := cond_isProbabilityMeasure (hpos _).ne'
  have hi : Integrable (Function.uncurry Y) (σ.prod μ) := Integrable.of_bound
    hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound p.1 p.2))
  have he (y : Ω) : charge (μ := μ) q Y x y =
      ∫ w, (∫ z, Y z w ∂σ) ∂cond μ (q ⁻¹' {q y}) := by
    let τ := cond μ (q ⁻¹' {q y})
    let : IsProbabilityMeasure τ := cond_isProbabilityMeasure (hpos _).ne'
    have hi' : Integrable (Function.uncurry Y) (σ.prod τ) := Integrable.of_bound
      hY.aestronglyMeasurable B (Eventually.of_forall (fun p => hbound p.1 p.2))
    exact integral_prod_symm _ hi'
  rw [integral_congr_ae (Eventually.of_forall he)]
  have hf : Integrable (fun w => ∫ z, Y z w ∂σ) μ := hi.integral_prod_right
  exact (integral_fiber_average q hq hpos _ hf).trans (integral_integral_swap hi).symm

/-- A row equation whose right side is constant on each actual fiber
survives the full conditional averaging. -/
theorem integral_charge_row_eq (q : Ω → ι) (hq : Measurable q)
    (hpos : ∀ i, 0 < μ (q ⁻¹' {i})) (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ)
    (hbound : ∀ x y, ‖Y x y‖ ≤ B) (s : ι → ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, Y x y ∂μ) = s (q x)) (x : Ω) :
    (∫ y, charge (μ := μ) q Y x y ∂μ) = s (q x) := by
  rw [integral_charge_row q hq hpos Y hY B hbound]
  let : IsProbabilityMeasure (cond μ (q ⁻¹' {q x})) :=
    cond_isProbabilityMeasure (hpos _).ne'
  calc
    _ = ∫ _, s (q x) ∂cond μ (q ⁻¹' {q x}) := by
      apply integral_congr_ae
      filter_upwards [cond_absolutelyContinuous.ae_le hrow,
        ae_cond_mem (hq (measurableSet_singleton (q x)))] with z hz hzx
      change q z = q x at hzx
      rw [hz, hzx]
    _ = _ := by simp

end Erdos1017.ConditionalAveraging
