module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomNeutralMove
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure

/-!
# Finite stationary rows of the four-region model

This module integrates the stationary rows over the four positive fibers,
identifies the own shifted operator rows with the finite charge matrix for the
neutral and block models, and derives strict floors of the present blocks above
the own multiplier with a positive own `gamma`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual finite partition integral, on the original carrier and law. -/
theorem integral_four_label_row (label : Ω → Fin 4) (hlabel : Measurable label)
    (f : Fin 4 → ℝ) :
    (∫ z, f (label z) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have heq : (fun z => f (label z)) =
      fun z => ∑ i : Fin 4, (label ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [heq, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

/-- Literal four positive fibers exhaust the original probability mass. -/
theorem four_fiber_masses_sum_one (label : Ω → Fin 4) (hlabel : Measurable label) :
    μ.real (label ⁻¹' {0}) + μ.real (label ⁻¹' {1}) +
      μ.real (label ⁻¹' {2}) + μ.real (label ⁻¹' {3}) = 1 := by
  have h := integral_four_label_row (μ := μ) label hlabel (fun _ => (1 : ℝ))
  simpa [Fin.sum_univ_succ, add_assoc] using h.symm

/-- Own AE row stationarity gives every actual finite label row. A row
is used only on its positive fiber and its actual common good event. -/
theorem finite_weighted_rows_of_stationary (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (K : Fin 4 → Fin 4 → ℝ) (nu : ℝ)
    (hrow : ∀ᵐ z ∂μ, (∫ w, K (label z) (label w) ∂μ) = nu) :
    ∀ i, (∑ j, μ.real (label ⁻¹' {j}) * K i j) = nu := by
  intro i
  obtain ⟨z, hz, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae hrow)
  change label z = i at hz
  rw [hz] at hgood
  exact (integral_four_label_row label hlabel (K i)).symm.trans hgood

/-- Exact pointwise moments identify the own actual shifted operator rows
with their literal finite charge matrix. No S or original multiplier occurs. -/
theorem finite_shifted_rows_of_fullStationaryClass
    {V : Model Ω μ} {m d c : ℝ} (hV : FullStationaryClass d c V m)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (Y : Fin 4 → Fin 4 → ℝ)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = Y (label p.1) (label p.2)) :
    ∀ i, (∑ j, μ.real (label ⁻¹' {j}) *
      (Y i j - m * (if blockAdjacency i j = true then 1 else 0))) = 2 * (c - m * d) := by
  apply finite_weighted_rows_of_stationary label hlabel hpositive
    (fun i j => Y i j - m * (if blockAdjacency i j = true then 1 else 0))
  filter_upwards [hV.stationary] with z hz
  convert hz using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => by
    change Y (label z) (label w) - m *
      (if blockAdjacency (label z) (label w) = true then 1 else 0) = shiftedMoment V m (z, w)
    rw [shiftedMoment_eq, (hmom (z, w)).1, (hmom (z, w)).2])

/-- The actual neutral model's own finite shifted rows match precisely
the t=1-delta,s=-h+delta equations used in the neutral strictness proof. -/
theorem fourRegionShiftedRows_of_neutral_stationary
    {V : Model Ω μ} {m d c : ℝ} (hV : FullStationaryClass d c V m)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (delta : ℝ)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = neutralBlockCharge x delta (label p.1) (label p.2)) :
    FourRegionShiftedRows x (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3}))
      (1 - delta) (-x 0 + delta) (-m) (2 * (c - m * d)) := by
  have hrows := finite_shifted_rows_of_fullStationaryClass hV label hlabel hpositive
    (neutralBlockCharge x delta) hmom
  apply (neutral_shifted_rows_iff x delta _ _ _ _ (-m) (2 * (c - m * d))).mp
  intro i
  have hi := hrows i
  have hm : (fun j : Fin 4 => μ.real (label ⁻¹' {j})) =
      ![μ.real (label ⁻¹' {0}), μ.real (label ⁻¹' {1}),
        μ.real (label ⁻¹' {2}), μ.real (label ⁻¹' {3})] := by
    funext j
    fin_cases j <;> rfl
  rw [← hm]
  simpa only [neg_mul, sub_eq_add_neg] using hi

/-- The ordinary active block model supplies its own literal four rows. -/
theorem fourRegionShiftedRows_of_block_stationary
    {V : Model Ω μ} {m d c : ℝ} (hV : FullStationaryClass d c V m)
    (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    FourRegionShiftedRows x (μ.real (label ⁻¹' {0})) (μ.real (label ⁻¹' {1}))
      (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3})) 1 (-x 0) (-m) (2 * (c - m * d)) := by
  have hzero : neutralBlockCharge x 0 = blockCharge x := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [neutralBlockCharge, blockCharge]
  have hmom0 : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = neutralBlockCharge x 0 (label p.1) (label p.2) := by
    simpa only [hzero] using hmom
  simpa only [sub_zero, add_zero] using
    fourRegionShiftedRows_of_neutral_stationary hV label hlabel hpositive x 0 hmom0

private theorem pair_property_of_positive_labels (label : Ω → Fin 4)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (P : Fin 4 → Fin 4 → Prop)
    (hP : ∀ᵐ p ∂μ.prod μ, P (label p.1) (label p.2)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨z, hz, hpz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hP))
  obtain ⟨w, hw, hpw⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive j).ne' (ae_restrict_of_ae hpz)
  exact hz ▸ hw ▸ hpw

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Own strict support on positive original pair blocks makes every
present finite charge strictly greater than its own multiplier. -/
theorem strict_present_block_floors_of_fullStationaryClass
    {V : Model Ω μ} {m d c : ℝ} (hV : FullStationaryClass d c V m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hpositive : ∀ i, 0 < μ (label ⁻¹' {i}))
    (Y : Fin 4 → Fin 4 → ℝ)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = Y (label p.1) (label p.2)) :
    ∀ i j, blockAdjacency i j = true → 0 < Y i j - m := by
  apply pair_property_of_positive_labels label hpositive
    (fun i j => blockAdjacency i j = true → 0 < Y i j - m)
  filter_upwards [(hV.strict_gap_structure hd hgap).strict_support] with p hp hG
  have hm := hmom p
  have hshift : 0 < shiftedMoment V m p := by
    by_contra h
    simp only [hm.1, hG, ite_true, h, ite_false] at hp
    norm_num at hp
  rw [shiftedMoment_eq, hm.1, hm.2, hG] at hshift
  simpa only [ite_true, mul_one] using hshift

/-- The ordinary active model derives the five actual present floors and
positive own gamma. No original S or original multiplier is used. -/
theorem own_block_present_floors
    {V : Model Ω μ} {m d c : ℝ} (hV : FullStationaryClass d c V m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 4) (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) :
    x 0 < -m ∧ x 2 < -m ∧ x 3 < -m ∧ x 4 < -m ∧ 0 < -m + x 1 ∧
      0 < 2 * (c - m * d) + m := by
  have hf := strict_present_block_floors_of_fullStationaryClass hV hd hgap label hpositive
    (blockCharge x) hmom
  have hAR := hf 0 2 rfl
  have hRR := hf 2 2 rfl
  have hEE := hf 3 3 rfl
  have hRE := hf 2 3 rfl
  have hBE := hf 1 3 rfl
  norm_num [blockCharge, Matrix.vecHead, Matrix.vecTail] at hAR hRR hEE hRE hBE
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    (hV.strict_gap_structure hd hgap).gamma_pos⟩

end Erdos1017.TwoAtomCountGate
