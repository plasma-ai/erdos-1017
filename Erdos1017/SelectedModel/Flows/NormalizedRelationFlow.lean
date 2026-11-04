module

public import Erdos1017.SelectedModel.Flows.MissingFlowDensity

/-!
# Normalized full flow along a relation

`normalizedDensity` distributes each source uniformly over its positive
recipient set, giving an integrable flow in which every positive source supplies
one unit, with mass equal to that of its positive sources, a mean-zero
direction, a nonnegative endpoint law and positive degree pairing under strict
degree order.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Original available receipt mass for a source in the second coordinate. -/
def columnMass (μ : Measure Ω) (Z : Set (Ω × Ω)) (y : Ω) : ℝ :=
  μ.real {x | (x, y) ∈ Z}

/-- Sources with a positive-measure recipient section in the original relation. -/
def positiveSources (μ : Measure Ω) (Z : Set (Ω × Ω)) : Set Ω :=
  {y | 0 < columnMass μ Z y}

/-- Distribute each source uniformly over its actual positive recipient section. -/
def normalizedDensity (μ : Measure Ω) (Z : Set (Ω × Ω)) : Ω × Ω → ℝ :=
  Z.indicator (fun p => (columnMass μ Z p.2)⁻¹)

/-- The available original section masses are measurable. -/
theorem measurable_columnMass (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    Measurable (columnMass μ Z) :=
  (measurable_measure_prodMk_right (μ := μ) hZ).ennreal_toReal

/-- The set of actual positive sources is measurable. -/
theorem measurableSet_positiveSources (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    MeasurableSet (positiveSources μ Z) :=
  measurableSet_lt measurable_const (measurable_columnMass Z hZ)

/-- The explicitly normalized product density is measurable. -/
theorem measurable_normalizedDensity (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    Measurable (normalizedDensity μ Z) :=
  ((measurable_columnMass Z hZ).comp measurable_snd).inv.indicator hZ

omit [IsFiniteMeasure μ] in
/-- The actual normalized density is nonnegative everywhere. -/
theorem normalizedDensity_nonneg (Z : Set (Ω × Ω)) (p : Ω × Ω) :
    0 ≤ normalizedDensity μ Z p := by
  by_cases hp : p ∈ Z
  · rw [normalizedDensity, indicator_of_mem hp]
    exact inv_nonneg.mpr measureReal_nonneg
  · rw [normalizedDensity, indicator_of_notMem hp]

omit [IsFiniteMeasure μ] in
/-- No new pair outside the original relation is used. -/
theorem normalizedDensity_eq_zero_of_notMem (Z : Set (Ω × Ω)) (p : Ω × Ω)
    (hp : p ∉ Z) : normalizedDensity μ Z p = 0 :=
  indicator_of_notMem hp _

/-- Each actual normalized source column is integrable, with no common bound
on reciprocals of the positive section masses. -/
theorem integrable_normalizedDensity_column (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (y : Ω) : Integrable (fun x => normalizedDensity μ Z (x, y)) μ := by
  change Integrable ({x | (x, y) ∈ Z}.indicator (fun _ => (columnMass μ Z y)⁻¹)) μ
  exact (integrable_const _).indicator (measurable_prodMk_right hZ)

omit [IsFiniteMeasure μ] in
/-- Every positive source supplies exactly one unit of its original density;
null sections supply zero. This is a pointwise identity of actual marginals. -/
theorem supply_normalizedDensity (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    supply μ (normalizedDensity μ Z) = (positiveSources μ Z).indicator (fun _ => 1) := by
  funext y
  have hsec : MeasurableSet {x | (x, y) ∈ Z} := measurable_prodMk_right hZ
  change (∫ x, {x | (x, y) ∈ Z}.indicator (fun _ => (columnMass μ Z y)⁻¹) x ∂μ) = _
  rw [integral_indicator hsec, setIntegral_const]
  change columnMass μ Z y * (columnMass μ Z y)⁻¹ = _
  by_cases hy : y ∈ positiveSources μ Z
  · rw [indicator_of_mem hy]
    exact mul_inv_cancel₀ (ne_of_gt hy)
  · have hzero : columnMass μ Z y = 0 :=
      le_antisymm (le_of_not_gt hy) measureReal_nonneg
    rw [indicator_of_notMem hy, hzero]
    simp

/-- Uniform redistribution over measurable recipient sections is a genuine
finite absolutely continuous flow, even with unbounded receipt density. -/
theorem integrable_normalizedDensity (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    Integrable (normalizedDensity μ Z) (μ.prod μ) := by
  apply (integrable_prod_iff' (measurable_normalizedDensity Z hZ).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (integrable_normalizedDensity_column Z hZ), ?_⟩
  have heq : (fun y => ∫ x, ‖normalizedDensity μ Z (x, y)‖ ∂μ) =
      (positiveSources μ Z).indicator (fun _ => 1) := by
    calc
      _ = supply μ (normalizedDensity μ Z) := by
        funext y
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => Real.norm_of_nonneg (normalizedDensity_nonneg Z (x, y)))
      _ = _ := supply_normalizedDensity Z hZ
  rw [heq]
  exact (integrable_const 1).indicator (measurableSet_positiveSources Z hZ)

/-- The actual flow mass is precisely the original mass of its positive sources. -/
theorem integral_normalizedDensity (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    (∫ p, normalizedDensity μ Z p ∂μ.prod μ) = μ.real (positiveSources μ Z) := by
  rw [← (integral_marginals (integrable_normalizedDensity Z hZ)).2,
    supply_normalizedDensity Z hZ, integral_indicator (measurableSet_positiveSources Z hZ),
    setIntegral_const]
  simp

omit [IsFiniteMeasure μ] in
/-- Normalized full supply is dominated by the original measure. -/
theorem supply_normalizedDensity_le_one (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (x : Ω) : supply μ (normalizedDensity μ Z) x ≤ 1 := by
  rw [supply_normalizedDensity Z hZ]
  by_cases hx : x ∈ positiveSources μ Z
  · simp only [indicator_of_mem hx, le_refl]
  · simp only [indicator_of_notMem hx, zero_le_one]

/-- The constructed full-flow direction has zero mean and a nonnegative
endpoint law. These are conclusions of the section construction. -/
theorem normalized_direction_properties (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) :
    Integrable (direction μ (normalizedDensity μ Z)) μ ∧
      (∫ x, direction μ (normalizedDensity μ Z) x ∂μ) = 0 ∧
      ∀ᵐ x ∂μ, -1 ≤ direction μ (normalizedDensity μ Z) x := by
  refine ⟨integrable_direction (integrable_normalizedDensity Z hZ),
    integral_direction (integrable_normalizedDensity Z hZ), ?_⟩
  exact direction_ge_neg_one (Eventually.of_forall (normalizedDensity_nonneg Z))
    (Eventually.of_forall (supply_normalizedDensity_le_one Z hZ))

omit [IsFiniteMeasure μ] in
/-- A relation receiving only in R has no receipt outside R, pointwise. -/
theorem receipt_normalizedDensity_eq_zero (Z : Set (Ω × Ω)) (R : Set Ω)
    (hR : ∀ p ∈ Z, p.1 ∈ R) (x : Ω) (hx : x ∉ R) :
    receipt μ (normalizedDensity μ Z) x = 0 := by
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall (fun y => normalizedDensity_eq_zero_of_notMem Z (x, y)
    (fun hxy => hx (hR (x, y) hxy)))

omit [IsFiniteMeasure μ] in
/-- Full supply removes its source from the endpoint whenever the recipient
side is disjoint there. No endpoint stationarity or optimality is asserted. -/
theorem normalized_endpoint_eq_zero (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (R : Set Ω) (hR : ∀ p ∈ Z, p.1 ∈ R)
    (x : Ω) (hx : x ∈ positiveSources μ Z) (hxR : x ∉ R) :
    1 + direction μ (normalizedDensity μ Z) x = 0 := by
  dsimp only [direction]
  rw [receipt_normalizedDensity_eq_zero Z R hR x hxR,
    supply_normalizedDensity Z hZ, indicator_of_mem hx]
  ring

/-- Positive original source mass and strict degree order make the
constructed full flow's original degree pairing strictly positive. -/
theorem normalized_degree_pairing_pos (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (hsource : 0 < μ (positiveSources μ Z))
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ)
    {B : ℝ} (hgBound : ∀ᵐ x ∂μ, ‖g x‖ ≤ B)
    (horder : ∀ᵐ p ∂μ.prod μ, p ∈ Z → g p.2 < g p.1) :
    0 < ∫ x, g x * direction μ (normalizedDensity μ Z) x ∂μ := by
  apply degree_pairing_pos (integrable_normalizedDensity Z hZ)
    (Eventually.of_forall (normalizedDensity_nonneg Z))
    (by rw [integral_normalizedDensity Z hZ]
        exact ENNReal.toReal_pos hsource.ne' (measure_ne_top μ _)) g hg hgBound
  filter_upwards [horder] with p hp hne
  apply hp
  by_contra hnot
  exact hne (normalizedDensity_eq_zero_of_notMem Z p hnot)

end Erdos1017.MissingFlow
