module

public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomOwnRowBounds
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockGeometry
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# The neutral competitor of the two-atom block

This module defines the neutral `AB`-down/`AR`-up charge matrix on the same
graph and its guarded count tests, and shows that it passes every count and
clique test on any carrier and sampling law, has the exact objective gain, and
has shifted rows matching the `u < b` row equations.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Classical

namespace Erdos1017.TwoAtomCountGate

/-- The genuine neutral AB-down/AR-up charge matrix on the same graph. -/
def neutralBlockCharge (x : Coefficients) (delta : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, 1 - delta, -x 0 + delta, 0], ![1 - delta, 0, x 0, x 1],
    ![-x 0 + delta, x 0, -x 2, -x 4], ![0, x 1, -x 4, -x 3]]

/-- The full guarded count tests for the neutral competitor. A-containing
cliques have no E labels because the physical A-E rectangle stays absent. -/
def neutralCountTest (x : Coefficients) (delta : ℝ) : Bool → Bool → ℕ → ℕ → ℝ
  | false, false, k, l => unanchoredTest k l x
  | false, true, k, l => countTest k l x
  | true, false, k, l => (-x 0 + delta) * k + unanchoredTest k l x
  | true, true, k, l => 1 - delta + delta * k + x 1 * l + unanchoredTest k l x

theorem neutral_block_charge_properties (x : Coefficients) (delta : ℝ) :
    (∀ i j, neutralBlockCharge x delta i j = neutralBlockCharge x delta j i) ∧
      ∀ i j, blockAdjacency i j = false → neutralBlockCharge x delta i j = 0 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [blockAdjacency, neutralBlockCharge]

/-- The small neutral move passes every actual count, including k=0,1
and the arbitrary high counts. -/
theorem neutral_count_tests (x : Coefficients) (hx : x ∈ feasible) (delta : ℝ)
    (hd : 0 ≤ delta) (hdh : delta ≤ x 0) (hdp : delta ≤ x 2) :
    ∀ A B k l, (A = true → l = 0) → neutralCountTest x delta A B k l ≤ 1 := by
  intro A B k l hAE
  cases A <;> cases B
  · exact hx.2.2.2.1 k l
  · exact hx.2.2.1 k l
  · have hl := hAE rfl
    subst l
    have hk : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
      simpa using TightCounts.gap_nonneg 0 k
    have hp := mul_nonneg hx.1 hk
    have hs := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdh) (Nat.cast_nonneg k)
    norm_num [neutralCountTest, unanchoredTest_apply]
    nlinarith only [hp, hs]
  · have hl := hAE rfl
    subst l
    simp only [neutralCountTest, Nat.cast_zero, mul_zero, add_zero]
    by_cases hk0 : k = 0
    · simp [hk0, unanchoredTest_apply]
      exact hd
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hsmall := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hk1)
      have hbin : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) - 2 * ((k : ℝ) - 1) := by
        by_cases h : k = 1
        · norm_num [h]
        · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
          nlinarith
      have hpen := mul_nonneg hx.1 hbin
      norm_num [unanchoredTest_apply]
      nlinarith only [hsmall, hpen]

/-- Exact finite charge inventory for the actual neutral matrix. No
clique or product-law assumption is needed for this identity. -/
theorem neutral_tupleCharge_eq_counts (x : Coefficients) (delta : ℝ)
    {n : ℕ} (v : Fin n → Fin 4) :
    let a : ℝ := PhysicalPrimal.labelCount v 0
    let b : ℝ := PhysicalPrimal.labelCount v 1
    let k : ℝ := PhysicalPrimal.labelCount v 2
    let l : ℝ := PhysicalPrimal.labelCount v 3
    FiniteArity.tupleCharge (neutralBlockCharge x delta) v =
      a * b * (1 - delta) + a * k * (-x 0 + delta) + b * k * x 0 + b * l * x 1 -
        x 2 * k * (k - 1) / 2 - x 3 * l * (l - 1) / 2 - x 4 * k * l := by
  have hterm (i j : Fin n) : (if i = j then 0 else neutralBlockCharge x delta (v i) (v j)) =
      neutralBlockCharge x delta (v i) (v j) -
        if i = j then neutralBlockCharge x delta (v i) (v j) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  change (∑ i, ∑ j, if i = j then 0 else neutralBlockCharge x delta (v i) (v j)) / 2 = _
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [PhysicalPrimal.sum_pairs_by_label,
    PhysicalPrimal.sum_by_label v (fun i => neutralBlockCharge x delta i i)]
  simp [neutralBlockCharge, Fin.sum_univ_succ]
  ring

/-- Every actual finite clique of the original graph passes the neutral
competitor's test. Atomic multiplicities and absent A-E pairs are derived. -/
theorem neutral_tupleCharge_le_one (x : Coefficients) (hx : x ∈ feasible) (delta : ℝ)
    (hd : 0 ≤ delta) (hdh : delta ≤ x 0) (hdp : delta ≤ x 2)
    {n : ℕ} (v : Fin n → Fin 4) (hclique : FiniteArity.TupleClique blockAdjacency v) :
    FiniteArity.tupleCharge (neutralBlockCharge x delta) v ≤ 1 := by
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
  have hcharge := neutral_tupleCharge_eq_counts x delta v
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · have ht := neutral_count_tests x hx delta hd hdh hdp false false
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3) (by simp)
      rw [ha, hb] at hcharge
      simp only [neutralCountTest, unanchoredTest_apply] at ht
      simp only [Nat.cast_zero, zero_mul, zero_sub, mul_zero, zero_add] at hcharge
      nlinarith only [hcharge, ht]
    · have ht := neutral_count_tests x hx delta hd hdh hdp false true
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3) (by simp)
      rw [ha, hb] at hcharge
      simp only [neutralCountTest, countTest_apply] at ht
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] at hcharge
      nlinarith only [hcharge, ht]
  · have hl := hAE ha
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · have ht := neutral_count_tests x hx delta hd hdh hdp true false
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3) (by intro _; exact hl)
      rw [ha, hb] at hcharge
      rw [hl] at ht hcharge
      simp only [neutralCountTest, unanchoredTest_apply] at ht
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_sub, mul_zero, one_mul] at hcharge
      nlinarith only [hcharge, ht]
    · have ht := neutral_count_tests x hx delta hd hdh hdp true true
        (PhysicalPrimal.labelCount v 2) (PhysicalPrimal.labelCount v 3) (by intro _; exact hl)
      rw [ha, hb] at hcharge
      rw [hl] at ht hcharge
      simp only [neutralCountTest, unanchoredTest_apply] at ht
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_sub, mul_zero, one_mul, mul_one]
        at hcharge
      nlinarith only [hcharge, ht]

/-- The actual same-graph neutral matrix has every full scalar test on
any carrier and sampling law, with no capped-feasibility assumption. -/
theorem neutral_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible) (delta : ℝ)
    (hd : 0 ≤ delta) (hdh : delta ≤ x 0) (hdp : delta ≤ x 2)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 4) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => neutralBlockCharge x delta (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv =>
    neutral_tupleCharge_le_one x hx delta hd hdh hdp (fun i => label (v i)) hv)

/-- Literal original weighted objective change of the neutral matrix. -/
theorem neutral_weighted_objective (x : Coefficients) (delta a b u e : ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      (![a, b, u, e] i) * (![a, b, u, e] j) * neutralBlockCharge x delta i j) / 2 =
      objective a b u e x + a * (u - b) * delta := by
  simp [neutralBlockCharge, Fin.sum_univ_succ, objective_apply]
  ring

/-- The actual original product-law objective of the neutral matrix has
its exact AB/AR gain. -/
theorem neutral_physicalObjective {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (label : Ω → Fin 4) (hlabel : Measurable label)
    (x : Coefficients) (delta : ℝ) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let u := μ.real (label ⁻¹' {2})
    let e := μ.real (label ⁻¹' {3})
    FiniteCappedSamplingCost.physicalObjective μ
      (fun z w => neutralBlockCharge x delta (label z) (label w)) =
        objective a b u e x + a * (u - b) * delta := by
  let q : Ω × Ω → Fin 4 × Fin 4 := fun p => (label p.1, label p.2)
  have hq : Measurable q := (hlabel.comp measurable_fst).prodMk
    (hlabel.comp measurable_snd)
  have heq : (fun p : Ω × Ω => neutralBlockCharge x delta (label p.1) (label p.2)) =
      fun p => ∑ ij : Fin 4 × Fin 4,
        (q ⁻¹' {ij}).indicator (fun _ => neutralBlockCharge x delta ij.1 ij.2) p := by
    funext p
    simp [q, Set.indicator_apply]
  have hi : (∫ p : Ω × Ω, neutralBlockCharge x delta (label p.1) (label p.2) ∂μ.prod μ) =
      ∑ i : Fin 4, ∑ j : Fin 4, μ.real (label ⁻¹' {i}) * μ.real (label ⁻¹' {j}) *
        neutralBlockCharge x delta i j := by
    rw [heq, integral_finsetSum Finset.univ (fun ij _ =>
      (integrable_const (neutralBlockCharge x delta ij.1 ij.2)).indicator
        (hq (measurableSet_singleton ij)))]
    simp_rw [integral_indicator (hq (measurableSet_singleton _)), setIntegral_const,
      smul_eq_mul]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hpre : q ⁻¹' {(i, j)} = (label ⁻¹' {i}) ×ˢ (label ⁻¹' {j}) := by
      ext p
      simp [q]
    rw [hpre, measureReal_prod_prod]
  have hm : (fun i : Fin 4 => μ.real (label ⁻¹' {i})) =
      ![μ.real (label ⁻¹' {0}), μ.real (label ⁻¹' {1}),
        μ.real (label ⁻¹' {2}), μ.real (label ⁻¹' {3})] := by
    funext i
    fin_cases i <;> rfl
  change (∫ p : Ω × Ω, neutralBlockCharge x delta (label p.1) (label p.2) ∂μ.prod μ) / 2 = _
  rw [hi]
  have hw := neutral_weighted_objective x delta (μ.real (label ⁻¹' {0}))
    (μ.real (label ⁻¹' {1})) (μ.real (label ⁻¹' {2})) (μ.real (label ⁻¹' {3}))
  rw [← hm] at hw
  exact hw

/-- The neutral matrix's finite weighted shifted rows are exactly the
literal row equations accepted by the strict-u<b numeric adapter. -/
theorem neutral_shifted_rows_iff (x : Coefficients) (delta a b u e ell nu : ℝ) :
    (∀ i : Fin 4, (∑ j : Fin 4, (![a, b, u, e] j) *
      (neutralBlockCharge x delta i j + ell * (if blockAdjacency i j = true then 1 else 0))) = nu) ↔
      FourRegionShiftedRows x a b u e (1 - delta) (-x 0 + delta) ell nu := by
  constructor
  · intro h
    constructor
    · have hi := h 0
      norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail] at hi
      nlinarith only [hi]
    · have hi := h 1
      norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail] at hi
      nlinarith only [hi]
    · have hi := h 2
      norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail] at hi
      nlinarith only [hi]
    · have hi := h 3
      norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail] at hi
      nlinarith only [hi]
  · intro h i
    fin_cases i
    · norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail]
      nlinarith only [h.A]
    · norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail]
      nlinarith only [h.B]
    · norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail]
      nlinarith only [h.R]
    · norm_num [neutralBlockCharge, blockAdjacency, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail]
      nlinarith only [h.E]

end Erdos1017.TwoAtomCountGate
