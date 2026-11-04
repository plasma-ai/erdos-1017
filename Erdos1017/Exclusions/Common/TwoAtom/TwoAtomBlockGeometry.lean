module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomCountSpace
public import Erdos1017.Multipartite.Physical.PhysicalLabelCounts
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Four-region block graph and its signed charge

This module defines the four-region graph on `A`, `B`, `R`, `E` (diffuse
diagonal blocks present, atomic ones absent) and its signed charge table in the
`AB = 1`, `AR = -BR` slice; the full signed count system licenses every clique
tuple on it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Erdos1017.TwoAtomCountGate

/-- The literal four-region graph, ordered as A, B, R, E. The diffuse
diagonal blocks are present; the two atomic diagonal blocks are absent. -/
def blockAdjacency : Fin 4 → Fin 4 → Bool :=
  ![![false, true, true, false], ![true, false, true, true],
    ![true, true, true, true], ![false, true, true, true]]

/-- The actual signed charge table in the AB=1, AR=-BR slice. -/
def blockCharge (x : Coefficients) : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1, -x 0, 0], ![1, 0, x 0, x 1],
    ![-x 0, x 0, -x 2, -x 4], ![0, x 1, -x 4, -x 3]]

/-- The literal graph and signed charge are symmetric, and the charge
vanishes on every absent block without any coefficient-sign premise. -/
theorem block_charge_properties (x : Coefficients) :
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

private theorem tupleCharge_eq_counts (x : Coefficients) {n : ℕ} (v : Fin n → Fin 4) :
    let a : ℝ := PhysicalPrimal.labelCount v 0
    let b : ℝ := PhysicalPrimal.labelCount v 1
    let k : ℝ := PhysicalPrimal.labelCount v 2
    let l : ℝ := PhysicalPrimal.labelCount v 3
    FiniteArity.tupleCharge (blockCharge x) v =
      a * b - a * k * x 0 + b * k * x 0 + b * l * x 1 -
        x 2 * k * (k - 1) / 2 - x 3 * l * (l - 1) / 2 - x 4 * k * l := by
  classical
  have hterm (i j : Fin n) : (if i = j then 0 else blockCharge x (v i) (v j)) =
      blockCharge x (v i) (v j) - if i = j then blockCharge x (v i) (v j) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  change (∑ i, ∑ j, if i = j then 0 else blockCharge x (v i) (v j)) / 2 = _
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [PhysicalPrimal.sum_pairs_by_label,
    PhysicalPrimal.sum_by_label v (fun i => blockCharge x i i)]
  simp [blockCharge, Fin.sum_univ_succ]
  ring

/-- A tuple with no A and exactly one B has its genuine B+kR+lE
charge. No clique or sign premise is needed for this exact identity. -/
theorem block_tupleCharge_eq_countTest (x : Coefficients) {n : ℕ} (v : Fin n → Fin 4)
    (hA : PhysicalPrimal.labelCount v 0 = 0) (hB : PhysicalPrimal.labelCount v 1 = 1) :
    FiniteArity.tupleCharge (blockCharge x) v =
      countTest (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3) x := by
  have h := tupleCharge_eq_counts x v
  rw [hA, hB] at h
  rw [h, countTest_apply]
  simp only [Nat.cast_zero, Nat.cast_one]
  ring

/-- The full signed count system licenses each actual clique tuple
pointwise, including tuples carried by a singular parent law. -/
theorem block_tupleCharge_le_one (x : Coefficients) (hx : x ∈ feasible)
    {n : ℕ} (v : Fin n → Fin 4) (hclique : FiniteArity.TupleClique blockAdjacency v) :
    FiniteArity.tupleCharge (blockCharge x) v ≤ 1 := by
  classical
  have ha : PhysicalPrimal.labelCount v 0 ≤ 1 := by
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hclique i j hij
    simp [hi, hj, blockAdjacency] at h
  have hb : PhysicalPrimal.labelCount v 1 ≤ 1 := by
    apply PhysicalPrimal.labelCount_le_one
    intro i j hi hj
    by_contra hij
    have h := hclique i j hij
    simp [hi, hj, blockAdjacency] at h
  have hAE : PhysicalPrimal.labelCount v 0 = 1 → PhysicalPrimal.labelCount v 3 = 0 := by
    intro ha
    have hex : ∃ i, v i = 0 := by
      by_contra h
      push Not at h
      simp [PhysicalPrimal.labelCount, h] at ha
    obtain ⟨i, hi⟩ := hex
    have hnot (j : Fin n) : v j ≠ 3 := by
      intro hj
      have hij : i ≠ j := fun h => by simp [h, hj] at hi
      have h := hclique i j hij
      simp [hi, hj, blockAdjacency] at h
    simp [PhysicalPrimal.labelCount, hnot]
  have hcharge := tupleCharge_eq_counts x v
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · rw [ha, hb] at hcharge
      have h := hx.2.2.2.1 (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
      rw [unanchoredTest_apply] at h
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_sub] at hcharge
      linarith only [hcharge, h]
    · rw [ha, hb] at hcharge
      have h := hx.2.2.1 (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3)
      rw [countTest_apply] at h
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_sub, one_mul] at hcharge
      linarith only [hcharge, h]
  · have hl := hAE ha
    rw [ha, hl] at hcharge
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · rw [hb] at hcharge
      have h := hx.2.2.2.2 (PhysicalPrimal.labelCount v 2)
      rw [firstAtomTest_apply] at h
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_zero, zero_sub,
        one_mul, add_zero] at hcharge
      linarith only [hcharge, h]
    · rw [hb] at hcharge
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_zero, one_mul,
        mul_one, add_zero] at hcharge
      have hk : 0 ≤ (PhysicalPrimal.labelCount v 2 : ℝ) *
          ((PhysicalPrimal.labelCount v 2 : ℝ) - 1) := by
        simpa using TightCounts.gap_nonneg 0 (PhysicalPrimal.labelCount v 2)
      have hp := mul_nonneg (hx.1) hk
      nlinarith only [hcharge, hp]

/-- Every actual tuple on the displayed four-region graph is licensed by
the full signed count system. No finite-order cutoff, sign restriction on
the star or mixed coefficients, sampling law or positive-cell hypothesis is used. -/
theorem block_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 4) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge x (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv => block_tupleCharge_le_one x hx (fun i => label (v i)) hv)

end Erdos1017.TwoAtomCountGate
