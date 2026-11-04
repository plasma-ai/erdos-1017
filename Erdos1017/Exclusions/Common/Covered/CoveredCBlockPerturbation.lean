module

public import Erdos1017.Exclusions.Common.Covered.CoveredCUniformSlack
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockGeometry
public import Erdos1017.SelectedModel.Capped.FiniteCappedSamplingCost

/-!
# Perturbation of the five-region C block

This module defines the five-region table on `A, B, C, R, E` with its adjacency
and charge, proves its clique tests at every order, and shows that the
simultaneous `BC`-up, `CR`-down, `CE`-down edit stays feasible on an interval of
radius `perturbRadius` with an exact objective slope.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CoveredC

open TwoAtomCountGate

/-- The five original regions are A, B, C, R, E. The three atomic
squares and the A-C and A-E rectangles are absent. -/
def blockAdjacency : Fin 5 → Fin 5 → Bool :=
  ![![false, true, false, true, false], ![true, false, true, true, true],
    ![false, true, false, true, true], ![true, true, true, true, true],
    ![false, true, true, true, true]]

/-- The original four-region charge with the secondary independent C
star and its two diffuse penalties retained literally. -/
def blockCharge (x : Coefficients) (t z d : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![0, 1, 0, -x 0, 0], ![1, 0, t, x 0, x 1],
    ![0, t, 0, -z, -d], ![-x 0, x 0, -z, -x 2, -x 4],
    ![0, x 1, -d, -x 4, -x 3]]

/-- Both tables are symmetric and the charge vanishes on absent blocks. -/
theorem block_properties (x : Coefficients) (t z d : ℝ) :
    (∀ i j, blockAdjacency i j = blockAdjacency j i) ∧
      (∀ i j, blockCharge x t z d i j = blockCharge x t z d j i) ∧
      ∀ i j, blockAdjacency i j = false → blockCharge x t z d i j = 0 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [blockAdjacency, blockCharge]

/-- Exact charge inventory, including every atomic and diffuse label. -/
theorem tupleCharge_eq_counts (x : Coefficients) (t z d : ℝ)
    {n : ℕ} (v : Fin n → Fin 5) :
    let a : ℝ := PhysicalPrimal.labelCount v 0
    let b : ℝ := PhysicalPrimal.labelCount v 1
    let c : ℝ := PhysicalPrimal.labelCount v 2
    let k : ℝ := PhysicalPrimal.labelCount v 3
    let l : ℝ := PhysicalPrimal.labelCount v 4
    FiniteArity.tupleCharge (blockCharge x t z d) v =
      a * b - a * k * x 0 + b * c * t + b * k * x 0 + b * l * x 1 -
        c * k * z - c * l * d - x 2 * k * (k - 1) / 2 -
        x 3 * l * (l - 1) / 2 - x 4 * k * l := by
  have hterm (i j : Fin n) : (if i = j then 0 else blockCharge x t z d (v i) (v j)) =
      blockCharge x t z d (v i) (v j) -
        if i = j then blockCharge x t z d (v i) (v j) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  change (∑ i, ∑ j, if i = j then 0 else blockCharge x t z d (v i) (v j)) / 2 = _
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [PhysicalPrimal.sum_pairs_by_label,
    PhysicalPrimal.sum_by_label v (fun i => blockCharge x t z d i i)]
  simp [blockCharge, Fin.sum_univ_succ]
  ring

private theorem count_le_one {n : ℕ} (v : Fin n → Fin 5)
    (hv : FiniteArity.TupleClique blockAdjacency v) (i : Fin 5)
    (hi : blockAdjacency i i = false) : PhysicalPrimal.labelCount v i ≤ 1 := by
  apply PhysicalPrimal.labelCount_le_one
  intro a b ha hb
  by_contra hab
  have h := hv a b hab
  simp [ha, hb, hi] at h

private theorem count_zero_of_absent {n : ℕ} (v : Fin n → Fin 5)
    (hv : FiniteArity.TupleClique blockAdjacency v) (i j : Fin 5) (hij : i ≠ j)
    (habsent : blockAdjacency i j = false) (hi : PhysicalPrimal.labelCount v i = 1) :
    PhysicalPrimal.labelCount v j = 0 := by
  have hex : ∃ a, v a = i := by
    by_contra h
    push Not at h
    simp [PhysicalPrimal.labelCount, h] at hi
  obtain ⟨a, ha⟩ := hex
  have hnot (b : Fin n) : v b ≠ j := by
    intro hb
    have hab : a ≠ b := fun h => hij (by simpa [h, hb] using ha.symm)
    have h := hv a b hab
    simp [ha, hb, habsent] at h
  simp [PhysicalPrimal.labelCount, hnot]

/-- Full C-free feasibility and the genuine rooted C counts license
all clique tuples. No hypothesis on multiplicities or absent pairs is used. -/
theorem tupleCharge_le_one (x : Coefficients) (hx : x ∈ feasible) (t z d : ℝ)
    (hz : 0 ≤ z) (hd : 0 ≤ d)
    (hcount : ∀ k l, countCharge t (x 0 - z) (x 1 - d) (x 2) (x 3) (x 4) k l ≤ 1)
    {n : ℕ} (v : Fin n → Fin 5) (hv : FiniteArity.TupleClique blockAdjacency v) :
    FiniteArity.tupleCharge (blockCharge x t z d) v ≤ 1 := by
  have ha := count_le_one v hv 0 rfl
  have hb := count_le_one v hv 1 rfl
  have hc := count_le_one v hv 2 rfl
  have hinv := tupleCharge_eq_counts x t z d v
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with hc | hc
  · rw [hc] at hinv
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha | ha
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
      · have h := hx.2.2.2.1 (PhysicalPrimal.labelCount v 3) (PhysicalPrimal.labelCount v 4)
        rw [unanchoredTest_apply] at h
        simp only [ha, hb, Nat.cast_zero, zero_mul, mul_zero, add_zero, sub_zero,
          zero_sub] at hinv
        linarith only [hinv, h]
      · have h := hx.2.2.1 (PhysicalPrimal.labelCount v 3) (PhysicalPrimal.labelCount v 4)
        rw [countTest_apply] at h
        simp only [ha, hb, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, add_zero,
          sub_zero, one_mul] at hinv
        linarith only [hinv, h]
    · have hl := count_zero_of_absent v hv 0 4 (by decide) rfl ha
      rw [ha, hl] at hinv
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
      · have h := hx.2.2.2.2 (PhysicalPrimal.labelCount v 3)
        rw [firstAtomTest_apply] at h
        simp only [hb, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, add_zero,
          sub_zero, zero_sub, one_mul] at hinv
        linarith only [hinv, h]
      · have hk : 0 ≤ (PhysicalPrimal.labelCount v 3 : ℝ) *
            ((PhysicalPrimal.labelCount v 3 : ℝ) - 1) := by
          simpa using TightCounts.gap_nonneg 0 (PhysicalPrimal.labelCount v 3)
        have hp := mul_nonneg hx.1 hk
        simp only [hb, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, add_zero,
          sub_zero, one_mul, mul_one] at hinv
        nlinarith only [hinv, hp]
  · have ha := count_zero_of_absent v hv 2 0 (by decide) rfl hc
    rw [ha, hc] at hinv
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb | hb
    · have h := hx.2.2.2.1 (PhysicalPrimal.labelCount v 3) (PhysicalPrimal.labelCount v 4)
      rw [unanchoredTest_apply] at h
      have hz' := mul_nonneg hz (show 0 ≤ (PhysicalPrimal.labelCount v 3 : ℝ) from
        Nat.cast_nonneg _)
      have hd' := mul_nonneg hd (show 0 ≤ (PhysicalPrimal.labelCount v 4 : ℝ) from
        Nat.cast_nonneg _)
      simp only [hb, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, add_zero,
        sub_zero, zero_sub, one_mul] at hinv
      nlinarith only [hinv, h, hz', hd']
    · have h := hcount (PhysicalPrimal.labelCount v 3) (PhysicalPrimal.labelCount v 4)
      unfold countCharge at h
      simp only [hb, Nat.cast_zero, Nat.cast_one, zero_mul, sub_zero, one_mul,
        mul_one] at hinv
      nlinarith only [hinv, h]

/-- Every order is licensed on any carrier and sampling law by the actual
pointwise clique tests of the five-region table. -/
theorem full_scalar_tests (x : Coefficients) (hx : x ∈ feasible) (t z d : ℝ)
    (hz : 0 ≤ z) (hd : 0 ≤ d)
    (hcount : ∀ k l, countCharge t (x 0 - z) (x 1 - d) (x 2) (x 3) (x 4) k l ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 5) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge x t z d (label a) (label b)) n := by
  intro n
  exact Eventually.of_forall (fun v hv =>
    tupleCharge_le_one x hx t z d hz hd hcount (fun i => label (v i)) hv)

/-- One concrete interval pays both the uniform count slack and the
nonnegative C penalties in the unrooted cliques. -/
def perturbRadius (s0 m0 z d : ℝ) : ℝ := min (min s0 (m0 - s0)) (min z d)

theorem perturbRadius_pos (s0 m0 z d : ℝ)
    (hs0 : 0 < s0) (hm0 : s0 < m0) (hz : 0 < z) (hd : 0 < d) :
    0 < perturbRadius s0 m0 z d := by
  exact lt_min (lt_min hs0 (sub_pos.mpr hm0)) (lt_min hz hd)

/-- The simultaneous BC-up/CR-down/CE-down edit passes every actual
sampled test on a fixed graph, for both signs throughout the stated interval. -/
theorem perturb_full_scalar_tests (x : Coefficients) (hx : x ∈ feasible)
    (t z d s0 m0 : ℝ) (ht : t = 1 - s0) (hs0 : 0 < s0) (hm0 : s0 < m0)
    (ha : x 0 - z ≤ s0) (hb : x 1 - d ≤ s0)
    (hp : m0 ≤ x 2) (hq : m0 ≤ x 3) (hr : m0 ≤ x 4)
    (eps : ℝ) (heps : |eps| ≤ perturbRadius s0 m0 z d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (label : Ω → Fin 5) :
    ∀ n, FiniteArity.FeasibleOrder μ
      (fun a b => blockAdjacency (label a) (label b))
      (fun a b => blockCharge x (t + eps) (z + eps) (d + eps) (label a) (label b)) n := by
  have hslack : |eps| ≤ min s0 (m0 - s0) := heps.trans (min_le_left _ _)
  have hpen : |eps| ≤ min z d := heps.trans (min_le_right _ _)
  have hz : 0 ≤ z + eps := by
    have h := (neg_le_neg (hpen.trans (min_le_left _ _))).trans (neg_abs_le eps)
    linarith
  have hd : 0 ≤ d + eps := by
    have h := (neg_le_neg (hpen.trans (min_le_right _ _))).trans (neg_abs_le eps)
    linarith
  apply full_scalar_tests x hx (t + eps) (z + eps) (d + eps) hz hd
  intro k l
  have h := countCharge_perturb_le_one t (x 0 - z) (x 1 - d)
    (x 2) (x 3) (x 4) s0 m0 ht hs0 hm0 ha hb hp hq hr eps hslack k l
  simpa only [sub_add_eq_sub_sub] using h

private theorem integral_label_pairs {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (label : Ω → Fin 5) (hlabel : Measurable label)
    (f : Fin 5 → Fin 5 → ℝ) :
    (∫ p : Ω × Ω, f (label p.1) (label p.2) ∂μ.prod μ) =
      ∑ i, ∑ j, μ.real (label ⁻¹' {i}) * μ.real (label ⁻¹' {j}) * f i j := by
  let q : Ω × Ω → Fin 5 × Fin 5 := fun p => (label p.1, label p.2)
  have hq : Measurable q := (hlabel.comp measurable_fst).prodMk (hlabel.comp measurable_snd)
  have heq : (fun p : Ω × Ω => f (label p.1) (label p.2)) =
      fun p => ∑ ij : Fin 5 × Fin 5, (q ⁻¹' {ij}).indicator (fun _ => f ij.1 ij.2) p := by
    funext p
    simp [q, Set.indicator_apply]
  rw [heq, integral_finsetSum Finset.univ (fun ij _ =>
    (integrable_const (f ij.1 ij.2)).indicator (hq (measurableSet_singleton ij)))]
  simp_rw [integral_indicator (hq (measurableSet_singleton _)), setIntegral_const, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hpre : q ⁻¹' {(i, j)} = (label ⁻¹' {i}) ×ˢ (label ⁻¹' {j}) := by
    ext p
    simp [q]
  rw [hpre, measureReal_prod_prod]

/-- Exact original-law objective, retaining the C mass and its original
three incident charge coefficients. No cell positivity is required. -/
theorem physicalObjective {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (label : Ω → Fin 5) (hlabel : Measurable label)
    (x : Coefficients) (t z d : ℝ) :
    let a := μ.real (label ⁻¹' {0})
    let b := μ.real (label ⁻¹' {1})
    let c := μ.real (label ⁻¹' {2})
    let u := μ.real (label ⁻¹' {3})
    let e := μ.real (label ⁻¹' {4})
    FiniteCappedSamplingCost.physicalObjective μ
      (fun v w => blockCharge x t z d (label v) (label w)) =
        objective a b u e x + c * (b * t - u * z - e * d) := by
  change (∫ p : Ω × Ω, blockCharge x t z d (label p.1) (label p.2) ∂μ.prod μ) / 2 = _
  rw [integral_label_pairs label hlabel, objective_apply]
  simp [blockCharge, Fin.sum_univ_succ]
  ring

/-- The genuine two-sided edit has the claimed exact objective slope on
any measurable partition under its original finite measure. -/
theorem perturb_physicalObjective {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (label : Ω → Fin 5) (hlabel : Measurable label)
    (x : Coefficients) (t z d eps : ℝ) :
    FiniteCappedSamplingCost.physicalObjective μ
      (fun v w => blockCharge x (t + eps) (z + eps) (d + eps) (label v) (label w)) =
        FiniteCappedSamplingCost.physicalObjective μ
          (fun v w => blockCharge x t z d (label v) (label w)) +
        eps * μ.real (label ⁻¹' {2}) *
          (μ.real (label ⁻¹' {1}) - μ.real (label ⁻¹' {3}) - μ.real (label ⁻¹' {4})) := by
  rw [physicalObjective label hlabel, physicalObjective label hlabel]
  ring

end Erdos1017.CoveredC
