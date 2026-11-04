module

public import Erdos1017.Exclusions.Common.Physical.PhysicalResidualCountTightness

/-!
# Counting diffuse vertices of parents with one child

The measure `childCountMeasure` keeps parents containing the independent child
exactly once and counts their diffuse vertices; its mass is the child cost mass,
its first count is the mixed pair demand, and parent events survive restriction
and pushforward.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.PhysicalPrimal

/-- Keep parents containing the independent child exactly once, then
count their diffuse vertices. The original cost measure is not normalized. -/
def childCountMeasure (θ : Measure (ℕ × ℕ)) : Measure ℕ :=
  (θ.restrict {z | z.1 = 1}).map Prod.snd

instance childCountMeasure_finite (θ : Measure (ℕ × ℕ)) [IsFiniteMeasure θ] :
    IsFiniteMeasure (childCountMeasure θ) := by
  unfold childCountMeasure
  infer_instance

theorem integral_childCountMeasure (θ : Measure (ℕ × ℕ)) (F : ℕ → ℝ) :
    (∫ n, F n ∂childCountMeasure θ) = ∫ z, if z.1 = 1 then F z.2 else 0 ∂θ := by
  rw [childCountMeasure, integral_map measurable_snd.aemeasurable
    (measurable_of_countable F).aestronglyMeasurable,
    ← integral_indicator ((Set.to_countable _).measurableSet)]
  simp only [Set.indicator_apply, mem_ofPred_eq]

theorem integrable_childCountMeasure (θ : Measure (ℕ × ℕ)) (F : ℕ → ℝ)
    (hi : Integrable (fun z : ℕ × ℕ => F z.2) θ) : Integrable F (childCountMeasure θ) := by
  apply (integrable_map_measure (measurable_of_countable F).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr
  exact hi.restrict

/-- Boolean child multiplicity identifies the exact child cost mass
with the first child-count demand on the unchanged original parents. -/
theorem childCountMeasure_mass (θ : Measure (ℕ × ℕ)) [IsFiniteMeasure θ]
    (hbool : ∀ᵐ z ∂θ, z.1 ≤ 1) :
    (childCountMeasure θ).real univ = ∫ z, (z.1 : ℝ) ∂θ := by
  have heq : (fun z : ℕ × ℕ => if z.1 = 1 then (1 : ℝ) else 0) =ᵐ[θ]
      (fun z => (z.1 : ℝ)) := by
    filter_upwards [hbool] with z hz
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hz with h | h <;> simp [h]
  calc
    _ = ∫ _ : ℕ, (1 : ℝ) ∂childCountMeasure θ := by simp
    _ = ∫ z, if z.1 = 1 then (1 : ℝ) else 0 ∂θ := integral_childCountMeasure θ (fun _ => 1)
    _ = _ := integral_congr_ae heq

/-- The child's first diffuse count is the original mixed pair demand. -/
theorem childCountMeasure_first (θ : Measure (ℕ × ℕ))
    (hbool : ∀ᵐ z ∂θ, z.1 ≤ 1) :
    (∫ n : ℕ, (n : ℝ) ∂childCountMeasure θ) = ∫ z, (z.1 : ℝ) * (z.2 : ℝ) ∂θ := by
  rw [integral_childCountMeasure]
  apply integral_congr_ae
  filter_upwards [hbool] with z hz
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hz with h | h <;> simp [h]

/-- Actual parent events survive restriction and pushforward without
an independence or absolute-continuity assumption on the joint laws. -/
theorem ae_childCountMeasure (θ : Measure (ℕ × ℕ)) (P : ℕ → Prop)
    (hP : ∀ᵐ z ∂θ, z.1 = 1 → P z.2) : ∀ᵐ n ∂childCountMeasure θ, P n := by
  apply (ae_map_iff measurable_snd.aemeasurable ((Set.to_countable _).measurableSet)).mpr
  exact (ae_restrict_iff' ((Set.to_countable _).measurableSet)).mpr hP

end Erdos1017.PhysicalPrimal
