module

public import Erdos1017.Exclusions.Common.Covered.CoveredZeroExteriorBlocks
public import Erdos1017.Exclusions.Common.FiniteBlockScalarModel
public import Erdos1017.Exclusions.Common.DeterministicFullStationarity

/-!
# Explicit optimum of the zero-exterior child

This module defines the `explicitDual` with adjacent contact counts `j` and
`j+1`, shows that nonnegative weights of its two count inequalities give the
sharp objective bound, that it has a boxed full-feasible model attaining the
original optimum, and that this model carries its own stationary multiplier and
row differences.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CoveredZeroExterior

/-- The two adjacent contact counts are j and j+1. -/
def explicitDual (j : ℕ) : Coefficients :=
  ![2 / ((j : ℝ) + 1), 2 / ((j : ℝ) * ((j : ℝ) + 1))]

theorem explicitDual_feasible (j : ℕ) (hj : 1 ≤ j) : explicitDual j ∈ feasible := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  refine ⟨by dsimp [explicitDual]; positivity, by dsimp [explicitDual]; positivity, ?_⟩
  intro n
  have h := TightCounts.gap_nonneg j n
  change (n : ℝ) * (2 / ((j : ℝ) + 1)) -
    (2 / ((j : ℝ) * ((j : ℝ) + 1))) * n * (n - 1) / 2 ≤ 1
  have heq : (n : ℝ) * (2 / ((j : ℝ) + 1)) -
      (2 / ((j : ℝ) * ((j : ℝ) + 1))) * n * (n - 1) / 2 =
      (n : ℝ) * (2 * j + 1 - n) / ((j : ℝ) * (j + 1)) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_one (mul_pos hj0 hj1)).mpr
  nlinarith

theorem exists_count_cell {b e : ℝ} (hb : 0 < b) (he : 0 < e) :
    ∃ j : ℕ, 1 ≤ j ∧ ((j : ℝ) - 1) * b ≤ e ∧ e ≤ j * b := by
  let j := ⌈e / b⌉₊
  have hj : 1 ≤ j := Nat.one_le_ceil_iff.mpr (div_pos he hb)
  have hlo := Nat.ceil_lt_add_one (div_nonneg he.le hb.le)
  have hhi := Nat.le_ceil (e / b)
  refine ⟨j, hj, ?_, ?_⟩
  · apply (le_div_iff₀ hb).mp
    dsimp only [j]
    linarith
  · exact (div_le_iff₀ hb).mp hhi

/-- Nonnegative weights of the two actual count inequalities give the
sharp objective bound. No optimal-face or contact certificate is assumed. -/
theorem objective_le_explicitDual {b e : ℝ} (he : 0 ≤ e)
    (j : ℕ) (hj : 1 ≤ j) (hlo : ((j : ℝ) - 1) * b ≤ e) (hhi : e ≤ j * b)
    (y : Coefficients) (hy : y ∈ feasible) :
    objective b e y ≤ objective b e (explicitDual j) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  let w := b * e - e ^ 2 / j
  let z := (e ^ 2 - ((j : ℝ) - 1) * b * e) / (j + 1)
  have hw : 0 ≤ w := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hj0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhi he]
  have hz : 0 ≤ z := by
    apply div_nonneg _ hj1.le
    nlinarith [mul_le_mul_of_nonneg_left hlo he]
  have h := add_le_add (mul_le_mul_of_nonneg_left (hy.2.2 j) hw)
    (mul_le_mul_of_nonneg_left (hy.2.2 (j + 1)) hz)
  simp only [mul_one, Nat.cast_add, Nat.cast_one] at h
  have hleft : w * ((j : ℝ) * y 0 - y 1 * j * (j - 1) / 2) +
      z * (((j : ℝ) + 1) * y 0 - y 1 * (j + 1) * ((j + 1) - 1) / 2) =
      objective b e y := by
    dsimp only [w, z, objective]
    field_simp
    ring
  have hright : w + z = objective b e (explicitDual j) := by
    dsimp only [w, z, objective, explicitDual]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rwa [hleft, hright] at h

theorem explicitDual_box (j : ℕ) (hj : 1 ≤ j) :
    ∀ i k, blockCharge (explicitDual j) i k ∈ Icc (-3 : ℝ) 1 := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  have hv0 : 0 ≤ 2 / ((j : ℝ) + 1) := by positivity
  have hv1 : 2 / ((j : ℝ) + 1) ≤ 1 := (div_le_one hj1).mpr (by linarith)
  have hq0 : 0 ≤ 2 / ((j : ℝ) * (j + 1)) := by positivity
  have hq1 : 2 / ((j : ℝ) * (j + 1)) ≤ 1 :=
    (div_le_one (mul_pos hj0 hj1)).mpr (by nlinarith)
  intro i k
  fin_cases i <;> fin_cases k <;>
    norm_num [blockCharge, explicitDual, Set.mem_Icc] <;> constructor <;> linarith

open CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The explicit dual has a genuine boxed full-feasible model. Equality
with the old optimum follows from its two-count upper bound and actual
full-feasible comparison, before any new multiplier is selected. -/
theorem exists_explicit_full_optimum [StandardBorelSpace Ω] [NullSingletonClass μ]
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (label : Ω → Fin 3) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    ∃ j : ℕ, 1 ≤ j ∧
      ((j : ℝ) - 1) * μ.real (label ⁻¹' {1}) ≤ μ.real (label ⁻¹' {2}) ∧
      μ.real (label ⁻¹' {2}) ≤ j * μ.real (label ⁻¹' {1}) ∧
      ∃ V : Model Ω μ, FullFeasible V ∧ density V = d ∧ CappedModel.objective V = c ∧
        (∀ p : Ω × Ω,
          V.moment CappedColor.adjacency p =
            (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
          V.moment CappedColor.charge p = blockCharge (explicitDual j) (label p.1) (label p.2)) ∧
        ∀ p, ∀ᵐ z ∂V.kernel p,
          CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  let a := μ.real (label ⁻¹' {0})
  let b := μ.real (label ⁻¹' {1})
  let e := μ.real (label ⁻¹' {2})
  have hb : 0 < b := ENNReal.toReal_pos (hpositive 1).ne' (measure_ne_top _ _)
  have he : 0 < e := ENNReal.toReal_pos (hpositive 2).ne' (measure_ne_top _ _)
  obtain ⟨j, hj, hlo, hhi⟩ := exists_count_cell hb he
  obtain ⟨V, hV, hVmom, hdV, hcV, hdet⟩ := exists_boxed_finite_block_model label hlabel
    blockAdjacency (block_properties (explicitDual j)).1 (blockCharge (explicitDual j))
    (block_properties (explicitDual j)).2.1 (block_properties (explicitDual j)).2.2
    (explicitDual_box j hj)
    (block_full_scalar_tests (explicitDual j) (explicitDual_feasible j hj) μ label)
  have hD : FiniteCappedSamplingCost.physicalDensity μ
      (fun x z => blockAdjacency (label x) (label z)) = d := by
    rw [← hW.density_eq]
    unfold FiniteCappedSamplingCost.physicalDensity density
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).1.symm))
  have hC : a * b + objective b e y = c := by
    rw [← block_physicalObjective label hlabel, ← hW.objective_eq]
    unfold FiniteCappedSamplingCost.physicalObjective CappedModel.objective
    congr 1
    exact integral_congr_ae (Eventually.of_forall (fun p => (hmom p).2.symm))
  have hdV' : density V = d := hdV.trans hD
  have hcV' : CappedModel.objective V = c := by
    apply le_antisymm
    · have h := fullFeasible_objective_le_densityLimit V hV
      rwa [hdV', ← hW.optimal] at h
    · rw [hcV, block_physicalObjective label hlabel, ← hC]
      exact add_le_add_right (objective_le_explicitDual he.le j hj hlo hhi y hy) _
  exact ⟨j, hj, hlo, hhi, V, hV, hdV', hcV', hVmom, hdet⟩

private theorem integral_labels (label : Ω → Fin 3) (hlabel : Measurable label)
    (f : Fin 3 → ℝ) :
    (∫ z, f (label z) ∂μ) = ∑ i, μ.real (label ⁻¹' {i}) * f i := by
  have he : (fun z => f (label z)) =
      fun z => ∑ i, (label ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hlabel (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hlabel (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem block_property_of_ae (label : Ω → Fin 3)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (P : Fin 3 → Fin 3 → Prop)
    (hP : ∀ᵐ p ∂μ.prod μ, P (label p.1) (label p.2)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨x, hx, hpx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hP))
  obtain ⟨z, hz, hpz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive j).ne' (ae_restrict_of_ae hpx)
  exact hx ▸ hz ▸ hpz

/-- Every finite shifted row comes from the own actual stationary event
on its positive original fiber. -/
theorem finite_rows_of_fullStationaryClass {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 3) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    ∀ i, (∑ j, μ.real (label ⁻¹' {j}) *
      (blockCharge y i j - m * (if blockAdjacency i j = true then 1 else 0))) =
        2 * (c - m * d) := by
  intro i
  obtain ⟨z, hz, hstat⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae hW.stationary)
  have hlabelz : label z = i := hz
  have heq : (∫ w, shiftedKernel W m z w ∂μ) =
      ∫ w, blockCharge y i (label w) - m *
        (if blockAdjacency i (label w) = true then 1 else 0) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun w => by
      rw [shiftedKernel, shiftedMoment_eq, (hmom (z, w)).1, (hmom (z, w)).2, hlabelz])
  rw [heq, integral_labels label hlabel (fun j => blockCharge y i j - m *
    (if blockAdjacency i j = true then 1 else 0))] at hstat
  exact hstat

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Own strict support on the positive original E square gives its
strict present-block penalty ceiling, without an original multiplier transfer. -/
theorem penalty_lt_own_multiplier {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 3) (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    y 1 < -m := by
  have hfinite := block_property_of_ae label hpositive
    (fun i j => blockAdjacency i j = true → 0 < blockCharge y i j - m) (by
      filter_upwards [(hW.strict_gap_structure hd hgap).strict_support] with p hp hG
      have hpos : 0 < shiftedMoment W m p := by
        by_contra h
        simp only [(hmom p).1, hG, ite_true, h, ite_false] at hp
        norm_num at hp
      rw [shiftedMoment_eq, (hmom p).1, (hmom p).2, hG] at hpos
      simpa only [ite_true, mul_one] using hpos)
  have h := hfinite 2 2 rfl
  norm_num [blockCharge] at h
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The A-E and B-A row differences use this model's own multiplier. -/
theorem stationary_row_differences {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m) (label : Ω → Fin 3) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    μ.real (label ⁻¹' {1}) * (1 - y 0) = μ.real (label ⁻¹' {2}) * (-m - y 1) ∧
      (μ.real (label ⁻¹' {0}) - μ.real (label ⁻¹' {1})) * (1 - m) +
        μ.real (label ⁻¹' {2}) * (y 0 - m) = 0 := by
  have hrows := finite_rows_of_fullStationaryClass hW label hlabel hpositive y hmom
  have hA := hrows 0
  have hB := hrows 1
  have hE := hrows 2
  norm_num [blockCharge, blockAdjacency, Fin.sum_univ_succ] at hA hB hE
  constructor <;> nlinarith only [hA, hB, hE]

/-- Select an own multiplier only after proving the explicit model attains
exactly the old optimum. No equality to the entry multiplier is asserted. -/
theorem exists_explicit_stationary_model {d c m : ℝ} {W : Model Ω μ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (label : Ω → Fin 3) (hlabel : Measurable label)
    (hpositive : ∀ i, 0 < μ (label ⁻¹' {i})) (y : Coefficients) (hy : y ∈ feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = blockCharge y (label p.1) (label p.2)) :
    ∃ j : ℕ, 1 ≤ j ∧
      ((j : ℝ) - 1) * μ.real (label ⁻¹' {1}) ≤ μ.real (label ⁻¹' {2}) ∧
      μ.real (label ⁻¹' {2}) ≤ j * μ.real (label ⁻¹' {1}) ∧
      ∃ (V : Model Ω μ) (m' : ℝ), FullStationaryClass d c V m' ∧
        (∀ p : Ω × Ω,
          V.moment CappedColor.adjacency p =
            (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
          V.moment CappedColor.charge p = blockCharge (explicitDual j) (label p.1) (label p.2)) ∧
        ∀ p, ∀ᵐ z ∂V.kernel p,
          CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  obtain ⟨j, hj, hlo, hhi, V, hV, hdV, hcV, hmomV, hdet⟩ :=
    exists_explicit_full_optimum hW label hlabel hpositive y hy hmom
  have hopt : CappedModel.objective V = FractionalGraph.densityLimit (density V) := by
    rw [hdV, hcV]; exact hW.optimal
  obtain ⟨m', hown⟩ := exists_same_model_fullStationaryClass V hV hopt hdet
    (hdV ▸ hd) (by rw [hdV, hcV]; exact hgap)
  rw [hdV, hcV] at hown
  exact ⟨j, hj, hlo, hhi, V, m', hown, hmomV, hdet⟩

end Erdos1017.CoveredZeroExterior
