module

public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorFace
public import Erdos1017.Multipartite.Physical.PhysicalLabelCounts
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Block tables for the one-exterior parent

This module defines the `R`-empty one-exterior-part parent on `A, B, C, E` with
its adjacency and charge, and the `C`-completed variant, and shows that the
Boolean `C`-count tests license every clique on the parent and that
repeated-label tests are pointwise clique tests on the completed graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredOneExterior

/-- The R-empty one-exterior-part parent, ordered as A,B,C,E. -/
def blockAdjacency : Fin 4 → Fin 4 → Bool :=
  ![![false, true, false, false], ![true, false, true, true],
    ![false, true, false, true], ![false, true, true, true]]

def blockCharge (y : Coefficients) : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, 0, 0], ![1, 0, y 0, y 1],
    ![0, y 0, 0, -y 2], ![0, y 1, -y 2, -y 3]]

theorem block_charge_properties (y : Coefficients) :
    (∀ i j, blockAdjacency i j = blockAdjacency j i) ∧
      (∀ i j, blockCharge y i j = blockCharge y j i) ∧
      ∀ i j, blockAdjacency i j = false → blockCharge y i j = 0 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [blockAdjacency, blockCharge]

/-- Completing only C changes its diagonal block and leaves A independent. -/
def repeatedAdjacency (i j : Fin 4) : Bool :=
  if i = 2 ∧ j = 2 then true else blockAdjacency i j

def repeatedCharge (y : Coefficients) (D : ℝ) (i j : Fin 4) : ℝ :=
  if i = 2 ∧ j = 2 then -D else blockCharge y i j

private theorem repeated_tupleCharge_eq_counts (y : Coefficients) (D : ℝ)
    {n : ℕ} (v : Fin n → Fin 4) :
    let a : ℝ := PhysicalPrimal.labelCount v 0
    let b : ℝ := PhysicalPrimal.labelCount v 1
    let r : ℝ := PhysicalPrimal.labelCount v 2
    let l : ℝ := PhysicalPrimal.labelCount v 3
    FiniteArity.tupleCharge (repeatedCharge y D) v =
      a * b + b * r * y 0 + b * l * y 1 - r * l * y 2 -
        y 3 * l * (l - 1) / 2 - D * r * (r - 1) / 2 := by
  have hterm (i j : Fin n) : (if i = j then 0 else repeatedCharge y D (v i) (v j)) =
      repeatedCharge y D (v i) (v j) -
        if i = j then repeatedCharge y D (v i) (v j) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  change (∑ i, ∑ j, if i = j then 0 else repeatedCharge y D (v i) (v j)) / 2 = _
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [PhysicalPrimal.sum_pairs_by_label,
    PhysicalPrimal.sum_by_label v (fun i => repeatedCharge y D i i)]
  simp [repeatedCharge, blockCharge, Fin.sum_univ_succ]
  ring

private theorem blockCharge_eq_repeated_zero (y : Coefficients) : blockCharge y = repeatedCharge y 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [repeatedCharge, blockCharge]

/-- On a B,C-containing clique the exact tuple charge is the true-state
child count test. The atomic A label is absent. -/
theorem block_tupleCharge_eq_test (y : Coefficients) {n : ℕ} (v : Fin n → Fin 4)
    (ha : PhysicalPrimal.labelCount v 0 = 0)
    (hb : PhysicalPrimal.labelCount v 1 = 1)
    (hc : PhysicalPrimal.labelCount v 2 = 1) :
    FiniteArity.tupleCharge (blockCharge y) v = test true (PhysicalPrimal.labelCount v 3) y := by
  rw [blockCharge_eq_repeated_zero, repeated_tupleCharge_eq_counts, ha, hb, hc]
  simp [test_eq_value, constant, slope, TightCounts.value]
  ring

private theorem repeated_clique_counts {n : ℕ} (v : Fin n → Fin 4)
    (hclique : FiniteArity.TupleClique repeatedAdjacency v) :
    PhysicalPrimal.labelCount v 0 ≤ 1 ∧ PhysicalPrimal.labelCount v 1 ≤ 1 ∧
      (PhysicalPrimal.labelCount v 0 = 1 →
        PhysicalPrimal.labelCount v 2 = 0 ∧ PhysicalPrimal.labelCount v 3 = 0) := by
  have hatom (a : Fin 4) (ha : a = 0 ∨ a = 1) : PhysicalPrimal.labelCount v a ≤ 1 := by
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hclique i j hij
    rcases ha with rfl | rfl <;> simp [hi, hj, repeatedAdjacency, blockAdjacency] at h
  refine ⟨hatom 0 (Or.inl rfl), hatom 1 (Or.inr rfl), ?_⟩
  intro ha
  have hex : ∃ i, v i = 0 := by
    by_contra h
    push Not at h
    simp [PhysicalPrimal.labelCount, h] at ha
  obtain ⟨i, hi⟩ := hex
  have hnot (c : Fin 4) (hc : c = 2 ∨ c = 3) (j : Fin n) : v j ≠ c := by
    intro hj
    have hij : i ≠ j := by
      intro h
      rcases hc with rfl | rfl <;> simp [h, hj] at hi
    have h := hclique i j hij
    rcases hc with rfl | rfl <;> simp [hi, hj, repeatedAdjacency, blockAdjacency] at h
  constructor
  · simp [PhysicalPrimal.labelCount, hnot 2 (Or.inl rfl)]
  · simp [PhysicalPrimal.labelCount, hnot 3 (Or.inr rfl)]

/-- All repeated-label tests are genuine pointwise clique tests on the
C-completed parent graph; the A atom is not completed. -/
theorem repeated_tupleCharge_le_one (y : Coefficients) (hy : y ∈ feasible)
    (D : ℝ) (hD : 0 ≤ D)
    (hfull : ∀ r n, repeatCharge (y 0) (y 1) (y 2) (y 3) D r n ≤ 1)
    {n : ℕ} (v : Fin n → Fin 4) (hclique : FiniteArity.TupleClique repeatedAdjacency v) :
    FiniteArity.tupleCharge (repeatedCharge y D) v ≤ 1 := by
  obtain ⟨ha, hb, hA⟩ := repeated_clique_counts v hclique
  rw [repeated_tupleCharge_eq_counts]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
  · rw [ha]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · rw [hb]
      have hr := TightCounts.gap_nonneg 0 (PhysicalPrimal.labelCount v 2)
      have hl := TightCounts.gap_nonneg 0 (PhysicalPrimal.labelCount v 3)
      have hp := mul_nonneg (hy.1 2) (mul_nonneg
        (Nat.cast_nonneg (PhysicalPrimal.labelCount v 2)) (Nat.cast_nonneg (PhysicalPrimal.labelCount v 3)))
      have hq := mul_nonneg (hy.1 3) (by simpa using hl :
        0 ≤ (PhysicalPrimal.labelCount v 3 : ℝ) * ((PhysicalPrimal.labelCount v 3 : ℝ) - 1))
      have hD' := mul_nonneg hD (by simpa using hr :
        0 ≤ (PhysicalPrimal.labelCount v 2 : ℝ) * ((PhysicalPrimal.labelCount v 2 : ℝ) - 1))
      norm_num only [Nat.cast_zero, zero_mul, zero_add]
      nlinarith only [hp, hq, hD']
    · rw [hb]
      have h := hfull (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
      unfold repeatCharge at h
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_add, one_mul]
      nlinarith only [h]
  · obtain ⟨hr, hl⟩ := hA ha
    rw [ha, hr, hl]
    have hb' : (PhysicalPrimal.labelCount v 1 : ℝ) ≤ 1 := by exact_mod_cast hb
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_zero, one_mul, add_zero]
    exact hb'

/-- Original Boolean C-count tests license every clique on the parent. -/
theorem block_tupleCharge_le_one (y : Coefficients) (hy : y ∈ feasible)
    {n : ℕ} (v : Fin n → Fin 4) (hclique : FiniteArity.TupleClique blockAdjacency v) :
    FiniteArity.tupleCharge (blockCharge y) v ≤ 1 := by
  have hclique' : FiniteArity.TupleClique repeatedAdjacency v := by
    intro i j hij
    unfold repeatedAdjacency
    split_ifs
    · rfl
    · exact hclique i j hij
  obtain ⟨ha, hb, hA⟩ := repeated_clique_counts v hclique'
  have hc : PhysicalPrimal.labelCount v 2 ≤ 1 := by
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hclique i j hij
    simp [hi, hj, blockAdjacency] at h
  rw [blockCharge_eq_repeated_zero, repeated_tupleCharge_eq_counts]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
  · rw [ha]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · rw [hb]
      have hpen := mul_nonneg (hy.1 2) (mul_nonneg
        (Nat.cast_nonneg (PhysicalPrimal.labelCount v 2)) (Nat.cast_nonneg (PhysicalPrimal.labelCount v 3)))
      have hl : 0 ≤ (PhysicalPrimal.labelCount v 3 : ℝ) *
          ((PhysicalPrimal.labelCount v 3 : ℝ) - 1) := by
        simpa using TightCounts.gap_nonneg 0 (PhysicalPrimal.labelCount v 3)
      have hq := mul_nonneg (hy.1 3) hl
      norm_num only [Nat.cast_zero, zero_mul, zero_add]
      nlinarith only [hpen, hq]
    · rw [hb]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with hc | hc
      · rw [hc]
        have h := hy.2 false (PhysicalPrimal.labelCount v 3)
        simp only [test_eq_value, constant, slope, TightCounts.value, Bool.false_eq_true,
          ↓reduceIte, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.proj_apply] at h
        norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, zero_add, one_mul, sub_zero]
        nlinarith only [h]
      · rw [hc]
        have h := hy.2 true (PhysicalPrimal.labelCount v 3)
        simp only [test_eq_value, constant, slope, TightCounts.value, ↓reduceIte,
          LinearMap.sub_apply, LinearMap.proj_apply] at h
        norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, zero_add, one_mul, sub_zero]
        nlinarith only [h]
  · obtain ⟨hr, hl⟩ := hA ha
    rw [ha, hr, hl]
    have hb' : (PhysicalPrimal.labelCount v 1 : ℝ) ≤ 1 := by exact_mod_cast hb
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_zero, one_mul, add_zero]
    exact hb'

theorem block_full_scalar_tests (y : Coefficients) (hy : y ∈ feasible)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 4) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge y (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv => block_tupleCharge_le_one y hy (fun i => label (v i)) hv)

end Erdos1017.CoveredOneExterior
