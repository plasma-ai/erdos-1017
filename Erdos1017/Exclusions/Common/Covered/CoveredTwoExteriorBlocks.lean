module

public import Erdos1017.Multipartite.Selector.VertexRepeat
public import Erdos1017.Multipartite.Physical.PhysicalLabelCounts
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Block tables for the two-exterior parent

This module defines the `R`-empty five-region parent on `A,B,C1,C2,E` with the
seven child coefficients `[t1,t2,v,c12,d1,d2,q]`, and shows that either repeat
witness yields a completed head, its affordable penalty and all scalar clique
orders on the same law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredTwoExterior

open VertexClassification

/-- The literal R-empty regions are A, B, C1, C2, E. A sees only B;
the four atoms are independent and the E square is complete. -/
def blockAdjacency : Fin 5 → Fin 5 → Bool :=
  ![![false, true, false, false, false], ![true, false, true, true, true],
    ![false, true, false, true, true], ![false, true, true, false, true],
    ![false, true, true, true, true]]

/-- The seven child coefficients keep the fixed order
[t1,t2,v,c12,d1,d2,q], with the fixed original AB charge one. -/
def blockCharge (x : Coefficients) : Fin 5 → Fin 5 → ℝ :=
  ![![0, 1, 0, 0, 0], ![1, 0, x 0, x 1, x 2],
    ![0, x 0, 0, -x 3, -x 4], ![0, x 1, -x 3, 0, -x 5],
    ![0, x 2, -x 4, -x 5, -x 6]]

theorem block_properties (x : Coefficients) :
    (∀ i j, blockAdjacency i j = blockAdjacency j i) ∧
      (∀ i j, blockCharge x i j = blockCharge x j i) ∧
      ∀ i j, blockAdjacency i j = false → blockCharge x i j = 0 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [blockAdjacency, blockCharge]

/-- Complete exactly the specified square; all original other blocks stay literal. -/
def repeatedAdjacency (i a b : Fin 5) : Bool :=
  if a = i ∧ b = i then true else blockAdjacency a b

/-- The specified completed square has the genuine mutual charge -D. -/
def repeatedCharge (x : Coefficients) (i : Fin 5) (D : ℝ) (a b : Fin 5) : ℝ :=
  if a = i ∧ b = i then -D else blockCharge x a b

theorem repeated_properties (x : Coefficients) (i : Fin 5) (D : ℝ) :
    (∀ a b, repeatedAdjacency i a b = repeatedAdjacency i b a) ∧
      (∀ a b, repeatedCharge x i D a b = repeatedCharge x i D b a) ∧
      ∀ a b, repeatedAdjacency i a b = false → repeatedCharge x i D a b = 0 := by
  obtain ⟨hG, hY, hzero⟩ := block_properties x
  constructor
  · intro a b
    simp only [repeatedAdjacency, and_comm, hG a b]
  constructor
  · intro a b
    simp only [repeatedCharge, and_comm, hY a b]
  · intro a b hab
    by_cases hi : a = i ∧ b = i
    · simp [repeatedAdjacency, hi] at hab
    · simp only [repeatedAdjacency, hi, ite_false] at hab
      simpa only [repeatedCharge, hi, ite_false] using hzero a b hab

/-- The exact physical inventory of a C1-completed tuple. C2 remains
single-use in its actual clique tests, and A is not completed. -/
theorem repeated_tupleCharge_eq_counts (x : Coefficients) (D : ℝ)
    {n : ℕ} (v : Fin n → Fin 5) :
    let a : ℝ := PhysicalPrimal.labelCount v 0
    let b : ℝ := PhysicalPrimal.labelCount v 1
    let r : ℝ := PhysicalPrimal.labelCount v 2
    let s : ℝ := PhysicalPrimal.labelCount v 3
    let l : ℝ := PhysicalPrimal.labelCount v 4
    FiniteArity.tupleCharge (repeatedCharge x 2 D) v =
      a * b + b * r * x 0 + b * s * x 1 + b * l * x 2 - r * s * x 3 -
        r * l * x 4 - s * l * x 5 - x 6 * l * (l - 1) / 2 - D * r * (r - 1) / 2 := by
  have hterm (i j : Fin n) : (if i = j then 0 else repeatedCharge x 2 D (v i) (v j)) =
      repeatedCharge x 2 D (v i) (v j) -
        if i = j then repeatedCharge x 2 D (v i) (v j) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  change (∑ i, ∑ j, if i = j then 0 else repeatedCharge x 2 D (v i) (v j)) / 2 = _
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [PhysicalPrimal.sum_pairs_by_label,
    PhysicalPrimal.sum_by_label v (fun i => repeatedCharge x 2 D i i)]
  simp [repeatedCharge, blockCharge, Fin.sum_univ_succ]
  ring

private theorem blockCharge_eq_repeated_zero (x : Coefficients) :
    blockCharge x = repeatedCharge x 2 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [repeatedCharge, blockCharge]

/-- Original tuple inventory before any clique restrictions are applied. -/
theorem tupleCharge_eq_counts (x : Coefficients) {n : ℕ} (v : Fin n → Fin 5) :
    let a : ℝ := PhysicalPrimal.labelCount v 0
    let b : ℝ := PhysicalPrimal.labelCount v 1
    let r : ℝ := PhysicalPrimal.labelCount v 2
    let s : ℝ := PhysicalPrimal.labelCount v 3
    let l : ℝ := PhysicalPrimal.labelCount v 4
    FiniteArity.tupleCharge (blockCharge x) v =
      a * b + b * r * x 0 + b * s * x 1 + b * l * x 2 - r * s * x 3 -
        r * l * x 4 - s * l * x 5 - x 6 * l * (l - 1) / 2 := by
  rw [blockCharge_eq_repeated_zero, repeated_tupleCharge_eq_counts]
  simp

private theorem repeated_clique_counts {n : ℕ} (v : Fin n → Fin 5)
    (hv : FiniteArity.TupleClique (repeatedAdjacency 2) v) :
    PhysicalPrimal.labelCount v 0 ≤ 1 ∧ PhysicalPrimal.labelCount v 1 ≤ 1 ∧
      PhysicalPrimal.labelCount v 3 ≤ 1 ∧
      (PhysicalPrimal.labelCount v 0 = 1 →
        PhysicalPrimal.labelCount v 2 = 0 ∧ PhysicalPrimal.labelCount v 3 = 0 ∧
          PhysicalPrimal.labelCount v 4 = 0) := by
  have hatom (a : Fin 5) (ha : a = 0 ∨ a = 1 ∨ a = 3) :
      PhysicalPrimal.labelCount v a ≤ 1 := by
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hv i j hij
    rcases ha with rfl | rfl | rfl <;>
      simp [hi, hj, repeatedAdjacency, blockAdjacency] at h
  refine ⟨hatom 0 (Or.inl rfl), hatom 1 (Or.inr (Or.inl rfl)),
    hatom 3 (Or.inr (Or.inr rfl)), ?_⟩
  intro ha
  have hex : ∃ i, v i = 0 := by
    by_contra h
    push Not at h
    simp [PhysicalPrimal.labelCount, h] at ha
  obtain ⟨i, hi⟩ := hex
  have hnot (a : Fin 5) (ha : a = 2 ∨ a = 3 ∨ a = 4) (j : Fin n) : v j ≠ a := by
    intro hj
    have hij : i ≠ j := by
      intro h
      rcases ha with rfl | rfl | rfl <;> simp [h, hj] at hi
    have h := hv i j hij
    rcases ha with rfl | rfl | rfl <;>
      simp [hi, hj, repeatedAdjacency, blockAdjacency] at h
  exact ⟨by simp [PhysicalPrimal.labelCount, hnot 2 (Or.inl rfl)],
    by simp [PhysicalPrimal.labelCount, hnot 3 (Or.inr (Or.inl rfl))],
    by simp [PhysicalPrimal.labelCount, hnot 4 (Or.inr (Or.inr rfl))]⟩

/-- Genuine all-count C1 repetition pays every actual clique, including
rootless tuples and the original independent A atom. -/
theorem repeated_tupleCharge_le_one (x : Coefficients) (hx : x ∈ feasible)
    (D : ℝ) (hD : 0 ≤ D)
    (hfull : ∀ r b n, b ≤ 1 →
      Repeat.oneSidedCharge (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) D r b n ≤ 1)
    {n : ℕ} (v : Fin n → Fin 5)
    (hv : FiniteArity.TupleClique (repeatedAdjacency 2) v) :
    FiniteArity.tupleCharge (repeatedCharge x 2 D) v ≤ 1 := by
  obtain ⟨ha, hb, hs, hA⟩ := repeated_clique_counts v hv
  rw [repeated_tupleCharge_eq_counts]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
  · rw [ha]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · rw [hb]
      have h := Repeat.rootlessCharge_nonpos (x 3) (x 4) (x 5) (x 6) D
        (hx.1 3) (hx.1 4) (hx.1 5) (hx.1 6) hD
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
        (PhysicalPrimal.labelCount v 4)
      norm_num only [Nat.cast_zero, zero_mul, zero_add]
      unfold Repeat.pairs at h
      nlinarith only [h]
    · rw [hb]
      have h := hfull (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
        (PhysicalPrimal.labelCount v 4) hs
      unfold Repeat.oneSidedCharge Repeat.pairs at h
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_add, one_mul]
      nlinarith only [h]
  · obtain ⟨hr, hs, hl⟩ := hA ha
    rw [ha, hr, hs, hl]
    have hb' : (PhysicalPrimal.labelCount v 1 : ℝ) ≤ 1 := by exact_mod_cast hb
    simpa only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_zero, one_mul,
      add_zero, zero_div] using hb'

/-- The original signed table obeys every actual clique test from the
seven-coordinate Boolean system, without a repetition premise. -/
theorem block_tupleCharge_le_one (x : Coefficients) (hx : x ∈ feasible)
    {n : ℕ} (v : Fin n → Fin 5) (hv : FiniteArity.TupleClique blockAdjacency v) :
    FiniteArity.tupleCharge (blockCharge x) v ≤ 1 := by
  have hv' : FiniteArity.TupleClique (repeatedAdjacency 2) v := by
    intro i j hij
    unfold repeatedAdjacency
    split_ifs
    · rfl
    · exact hv i j hij
  obtain ⟨ha, hb, hs, hA⟩ := repeated_clique_counts v hv'
  have hr : PhysicalPrimal.labelCount v 2 ≤ 1 := by
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hv i j hij
    simp [hi, hj, blockAdjacency] at h
  rw [tupleCharge_eq_counts]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
  · rw [ha]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · rw [hb]
      have h := Repeat.rootlessCharge_nonpos (x 3) (x 4) (x 5) (x 6) 0
        (hx.1 3) (hx.1 4) (hx.1 5) (hx.1 6) le_rfl
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
        (PhysicalPrimal.labelCount v 4)
      norm_num only [Nat.cast_zero, zero_mul, zero_add]
      unfold Repeat.pairs at h
      nlinarith only [h]
    · rw [hb]
      have h := VertexRepeat.original_boolean_feasibility x hx
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
        (PhysicalPrimal.labelCount v 4) hr hs
      unfold Repeat.oneSidedCharge Repeat.pairs at h
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_add, one_mul]
      nlinarith only [h]
  · obtain ⟨hr, hs, hl⟩ := hA ha
    rw [ha, hr, hs, hl]
    have hb' : (PhysicalPrimal.labelCount v 1 : ℝ) ≤ 1 := by exact_mod_cast hb
    simpa only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_zero, one_mul,
      add_zero, zero_div] using hb'

theorem block_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 5) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge x (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv => block_tupleCharge_le_one x hx (fun i => label (v i)) hv)

theorem repeated_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible)
    (D : ℝ) (hD : 0 ≤ D)
    (hfull : ∀ r b n, b ≤ 1 →
      Repeat.oneSidedCharge (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) D r b n ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 5) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => repeatedAdjacency 2 (label a) (label b))
      (fun a b => repeatedCharge x 2 D (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv =>
    repeated_tupleCharge_le_one x hx D hD hfull (fun i => label (v i)) hv)

/-- Swap exactly the two original exterior labels. A, B and E stay fixed. -/
def swapLabel : Fin 5 → Fin 5 := ![0, 1, 3, 2, 4]

theorem swapLabel_involutive : Function.Involutive swapLabel := by
  intro i
  fin_cases i <;> rfl

theorem block_swap (x : Coefficients) (i j : Fin 5) :
    blockAdjacency (swapLabel i) (swapLabel j) = blockAdjacency i j ∧
      blockCharge (VertexRepeat.swap x) (swapLabel i) (swapLabel j) = blockCharge x i j := by
  fin_cases i <;> fin_cases j <;> simp [swapLabel, blockAdjacency, blockCharge, VertexRepeat.swap]

theorem repeated_swap (x : Coefficients) (D : ℝ) (i j : Fin 5) :
    repeatedAdjacency 2 (swapLabel i) (swapLabel j) = repeatedAdjacency 3 i j ∧
      repeatedCharge (VertexRepeat.swap x) 2 D (swapLabel i) (swapLabel j) =
        repeatedCharge x 3 D i j := by
  fin_cases i <;> fin_cases j <;>
    simp [swapLabel, repeatedAdjacency, repeatedCharge, blockAdjacency, blockCharge,
      VertexRepeat.swap]

/-- Repeating C2 is licensed by the same one-sided count system
with its coefficient and label swaps both made explicit. -/
theorem second_repeated_tupleCharge_le_one (x : Coefficients) (hx : x ∈ feasible)
    (D : ℝ) (hD : 0 ≤ D)
    (hfull : ∀ r b n, b ≤ 1 →
      Repeat.oneSidedCharge (x 1) (x 0) (x 2) (x 3) (x 5) (x 4) (x 6) D r b n ≤ 1)
    {n : ℕ} (v : Fin n → Fin 5)
    (hv : FiniteArity.TupleClique (repeatedAdjacency 3) v) :
    FiniteArity.tupleCharge (repeatedCharge x 3 D) v ≤ 1 := by
  have hfull' : ∀ r b n, b ≤ 1 →
      Repeat.oneSidedCharge ((VertexRepeat.swap x) 0) ((VertexRepeat.swap x) 1)
        ((VertexRepeat.swap x) 2) ((VertexRepeat.swap x) 3) ((VertexRepeat.swap x) 4)
        ((VertexRepeat.swap x) 5) ((VertexRepeat.swap x) 6) D r b n ≤ 1 := by
    simpa [VertexRepeat.swap] using hfull
  have hv' : FiniteArity.TupleClique (repeatedAdjacency 2) (fun i => swapLabel (v i)) := by
    intro i j hij
    rw [(repeated_swap x D (v i) (v j)).1]
    exact hv i j hij
  have ht := repeated_tupleCharge_le_one (VertexRepeat.swap x)
    (VertexRepeat.swap_feasible x hx) D hD hfull' (fun i => swapLabel (v i)) hv'
  have heq : FiniteArity.tupleCharge (repeatedCharge (VertexRepeat.swap x) 2 D)
      (fun i => swapLabel (v i)) = FiniteArity.tupleCharge (repeatedCharge x 3 D) v := by
    unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
    simp_rw [(repeated_swap x D _ _).2]
  rwa [heq] at ht

theorem second_repeated_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible)
    (D : ℝ) (hD : 0 ≤ D)
    (hfull : ∀ r b n, b ≤ 1 →
      Repeat.oneSidedCharge (x 1) (x 0) (x 2) (x 3) (x 5) (x 4) (x 6) D r b n ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 5) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => repeatedAdjacency 3 (label a) (label b))
      (fun a b => repeatedCharge x 3 D (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv =>
    second_repeated_tupleCharge_le_one x hx D hD hfull (fun i => label (v i)) hv)

/-- Either actual repeat witness yields a concrete completed original
head, its affordable penalty and all scalar clique orders on the same law. -/
theorem exists_repeated_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible)
    (h : VertexRepeat.HasRepeat x ∨ VertexRepeat.HasRepeat (VertexRepeat.swap x))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 5) :
    ∃ (i : Fin 5) (D : ℝ), (i = 2 ∨ i = 3) ∧ 0 ≤ D ∧ D ≤ x 3 ∧
      ∀ n, FiniteArity.FeasibleOrder μ
        (fun a b => repeatedAdjacency i (label a) (label b))
        (fun a b => repeatedCharge x i D (label a) (label b)) n := by
  rcases h with ⟨D, hD, hbound, hfull⟩ | ⟨D, hD, hbound, hfull⟩
  · exact ⟨2, D, Or.inl rfl, hD, hbound, repeated_full_scalar_tests x hx D hD hfull μ label⟩
  · refine ⟨3, D, Or.inr rfl, hD, ?_, second_repeated_full_scalar_tests x hx D hD ?_ μ label⟩
    · simpa [VertexRepeat.swap] using hbound
    · simpa [VertexRepeat.swap] using hfull

end Erdos1017.CoveredTwoExterior
