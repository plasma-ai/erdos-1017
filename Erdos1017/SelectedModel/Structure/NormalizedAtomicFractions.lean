module

public import Erdos1017.SelectedModel.Flows.NormalizedRelationFlow
public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentCompactness
public import Mathlib.Tactic.Positivity

/-!
# Normalized fractions of a relation column

This module defines the section masses of a relation at a source, the allowed
labels with positive mass, and the fraction `rawFraction` of the normalized
column assigned to a part, and constructs from normalized columns a feasible
restricted `L²` assignment satisfying every finite-pattern constraint.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace Erdos1017.MissingFlow.NormalizedAtomicFractions

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Original relation mass in one recipient part at a fixed source. -/
def atomSectionMass (μ : Measure Ω) (Z : Set (Ω × Ω)) (I : ℕ → Set Ω)
    (i : ℕ) (y : Ω) : ℝ :=
  μ.real (I i ∩ {x | (x, y) ∈ Z})

/-- Original relation mass in the literal complement of all recipient parts. -/
def remainderSectionMass (μ : Measure Ω) (Z : Set (Ω × Ω)) (I : ℕ → Set Ω)
    (y : Ω) : ℝ :=
  μ.real ((⋃ i, I i)ᶜ ∩ {x | (x, y) ∈ Z})

/-- Labels with positive original relation mass at this source. -/
def allowed (μ : Measure Ω) (Z : Set (Ω × Ω)) (I : ℕ → Set Ω) (i : ℕ) : Set Ω :=
  {y | 0 < atomSectionMass μ Z I i y}

/-- The literal fraction of the normalized original column assigned to a part. -/
def rawFraction (μ : Measure Ω) (Z : Set (Ω × Ω)) (I : ℕ → Set Ω)
    (i : ℕ) (y : Ω) : ℝ :=
  atomSectionMass μ Z I i y / columnMass μ Z y

omit [IsFiniteMeasure μ] in
/-- The normalized fraction is the actual integral of the old normalized
product density over the original recipient part, at every source. -/
theorem rawFraction_eq_setIntegral_normalizedDensity
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (I : ℕ → Set Ω) (i : ℕ) (y : Ω) :
    rawFraction μ Z I i y = ∫ x in I i, normalizedDensity μ Z (x, y) ∂μ := by
  have hs : MeasurableSet {x | (x, y) ∈ Z} := measurable_prodMk_right hZ
  change rawFraction μ Z I i y =
    ∫ x in I i, {x | (x, y) ∈ Z}.indicator (fun _ => (columnMass μ Z y)⁻¹) x ∂μ
  rw [integral_indicator hs, setIntegral_const, measureReal_restrict_apply hs]
  simp only [rawFraction, atomSectionMass, smul_eq_mul, div_eq_mul_inv]
  rw [Set.inter_comm {x | (x, y) ∈ Z} (I i)]

private theorem measurable_sectionMass (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (A : Set Ω) (hA : MeasurableSet A) :
    Measurable (fun y => μ.real (A ∩ {x | (x, y) ∈ Z})) := by
  have hm := measurable_columnMass (μ := μ) ((A ×ˢ univ) ∩ Z)
    ((hA.prod MeasurableSet.univ).inter hZ)
  convert hm using 1
  funext y
  congr 1
  ext x
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true, mem_ofPred_eq]

private theorem measurable_atomSectionMass (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i)) (i : ℕ) :
    Measurable (atomSectionMass μ Z I i) :=
  measurable_sectionMass Z hZ (I i) (hI i)

private theorem measurable_remainderSectionMass (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i)) :
    Measurable (remainderSectionMass μ Z I) :=
  measurable_sectionMass Z hZ _ (MeasurableSet.iUnion hI).compl

private theorem measurableSet_allowed (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i)) (i : ℕ) :
    MeasurableSet (allowed μ Z I i) :=
  measurableSet_lt measurable_const (measurable_atomSectionMass Z hZ I hI i)

private theorem measurable_rawFraction (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i)) (i : ℕ) :
    Measurable (rawFraction μ Z I i) :=
  (measurable_atomSectionMass Z hZ I hI i).div (measurable_columnMass Z hZ)

private theorem rawFraction_box (Z : Set (Ω × Ω)) (I : ℕ → Set Ω) (i : ℕ) (y : Ω) :
    rawFraction μ Z I i y ∈ Icc (0 : ℝ) 1 := by
  have hN : 0 ≤ atomSectionMass μ Z I i y := measureReal_nonneg
  have hC : 0 ≤ columnMass μ Z y := measureReal_nonneg
  have hle : atomSectionMass μ Z I i y ≤ columnMass μ Z y :=
    measureReal_mono inter_subset_right
  constructor
  · exact div_nonneg hN hC
  · by_cases hz : columnMass μ Z y = 0
    · simp only [rawFraction, hz, div_zero, zero_le_one]
    · exact (div_le_one₀ (lt_of_le_of_ne hC (Ne.symm hz))).mpr hle

omit [IsFiniteMeasure μ] in
private theorem rawFraction_zero_of_notMem (Z : Set (Ω × Ω)) (I : ℕ → Set Ω)
    (i : ℕ) (y : Ω) (hy : y ∉ allowed μ Z I i) : rawFraction μ Z I i y = 0 := by
  have hN : atomSectionMass μ Z I i y = 0 :=
    le_antisymm (le_of_not_gt hy) measureReal_nonneg
  simp only [rawFraction, hN, zero_div]

private theorem rawFraction_zero_of_null (Z : Set (Ω × Ω)) (I : ℕ → Set Ω)
    (i : ℕ) (hi : μ (I i) = 0) (y : Ω) : rawFraction μ Z I i y = 0 := by
  have hle : atomSectionMass μ Z I i y ≤ μ.real (I i) :=
    measureReal_mono inter_subset_left
  have hzero : atomSectionMass μ Z I i y = 0 := by
    have hm : μ.real (I i) = 0 := by simp only [measureReal_def, hi, ENNReal.toReal_zero]
    exact le_antisymm (hm ▸ hle) measureReal_nonneg
  simp only [rawFraction, hzero, zero_div]

private theorem atomSectionMass_sum (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j))) (J : Finset ℕ) (y : Ω) :
    (∑ i ∈ J, atomSectionMass μ Z I i y) =
      μ.real (⋃ i ∈ J, I i ∩ {x | (x, y) ∈ Z}) := by
  apply (measureReal_biUnion_finset ?_ ?_).symm
  · intro i hi j hj hij
    exact (hdisjoint hij).mono inter_subset_left inter_subset_left
  · intro i _
    exact (hI i).inter (measurable_prodMk_right hZ)

private theorem rawFraction_partial_sum (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j))) (J : Finset ℕ) (y : Ω) :
    (∑ i ∈ J, rawFraction μ Z I i y) ≤ 1 := by
  have hle : (∑ i ∈ J, atomSectionMass μ Z I i y) ≤ columnMass μ Z y := by
    rw [atomSectionMass_sum Z hZ I hI hdisjoint J y]
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hx⟩
    rcases mem_iUnion.mp hx with ⟨_, hx⟩
    exact hx.2
  rw [show (∑ i ∈ J, rawFraction μ Z I i y) =
    (∑ i ∈ J, atomSectionMass μ Z I i y) / columnMass μ Z y by
      simp only [rawFraction, Finset.sum_div]]
  by_cases hz : columnMass μ Z y = 0
  · simp only [hz, div_zero, zero_le_one]
  · exact (div_le_one₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))).mpr hle

omit [IsFiniteMeasure μ] in
private theorem column_partition (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j))) (y : Ω) :
    μ {x | (x, y) ∈ Z} = μ ((⋃ i, I i)ᶜ ∩ {x | (x, y) ∈ Z}) +
      ∑' i, μ (I i ∩ {x | (x, y) ∈ Z}) := by
  let C : Set Ω := {x | (x, y) ∈ Z}
  have hC : MeasurableSet C := measurable_prodMk_right hZ
  have hparts : Pairwise (fun i j => Disjoint (I i ∩ C) (I j ∩ C)) :=
    fun _ _ hij => (hdisjoint hij).mono inter_subset_left inter_subset_left
  have hrem : Disjoint ((⋃ i, I i)ᶜ ∩ C) (⋃ i, I i ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact hx.1 (mem_iUnion.mpr ⟨i, hi.1⟩)
  have hcover : C = ((⋃ i, I i)ᶜ ∩ C) ∪ ⋃ i, I i ∩ C := by
    ext x
    constructor
    · intro hx
      by_cases hi : x ∈ ⋃ i, I i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hi
        exact Or.inr (mem_iUnion.mpr ⟨i, hi, hx⟩)
      · exact Or.inl ⟨hi, hx⟩
    · rintro (hx | hx)
      · exact hx.2
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact hi.2
  calc
    μ C = μ (((⋃ i, I i)ᶜ ∩ C) ∪ ⋃ i, I i ∩ C) := congrArg μ hcover
    _ = μ ((⋃ i, I i)ᶜ ∩ C) + μ (⋃ i, I i ∩ C) :=
      measure_union hrem (MeasurableSet.iUnion (fun i => (hI i).inter hC))
    _ = _ := by rw [measure_iUnion hparts (fun i => (hI i).inter hC)]

private theorem rawFraction_full_pattern (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j))) (J : Finset ℕ) (y : Ω)
    (hyH : y ∈ positiveSources μ Z)
    (hyJ : y ∈ ReverseAssignment.finitePattern (allowed μ Z I)
      (remainderSectionMass μ Z I) J) :
    (∑ i ∈ J, rawFraction μ Z I i y) = 1 := by
  change remainderSectionMass μ Z I y = 0 ∧
    ∀ i, i ∈ J ↔ 0 < atomSectionMass μ Z I i y at hyJ
  have hrem : μ ((⋃ i, I i)ᶜ ∩ {x | (x, y) ∈ Z}) = 0 := by
    calc
      _ = ENNReal.ofReal (remainderSectionMass μ Z I y) := (ofReal_measureReal).symm
      _ = 0 := by rw [hyJ.1, ENNReal.ofReal_zero]
  have hoff (i : ℕ) (hi : i ∉ J) : μ (I i ∩ {x | (x, y) ∈ Z}) = 0 := by
    have hN : atomSectionMass μ Z I i y = 0 := by
      apply le_antisymm _ measureReal_nonneg
      apply le_of_not_gt
      exact fun hpos => hi ((hyJ.2 i).mpr hpos)
    calc
      _ = ENNReal.ofReal (atomSectionMass μ Z I i y) := (ofReal_measureReal).symm
      _ = 0 := by rw [hN, ENNReal.ofReal_zero]
  have hfinite : μ {x | (x, y) ∈ Z} = ∑ i ∈ J, μ (I i ∩ {x | (x, y) ∈ Z}) := by
    rw [column_partition Z hZ I hI hdisjoint y, hrem, zero_add, tsum_eq_sum (s := J) hoff]
  have hreal : columnMass μ Z y = ∑ i ∈ J, atomSectionMass μ Z I i y := by
    have h := congrArg ENNReal.toReal hfinite
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)] at h
    exact h
  have hC : 0 < columnMass μ Z y := hyH
  calc
    _ = (∑ i ∈ J, atomSectionMass μ Z I i y) / columnMass μ Z y := by
      simp only [rawFraction, Finset.sum_div]
    _ = columnMass μ Z y / columnMass μ Z y := by rw [← hreal]
    _ = 1 := div_self hC.ne'

/-- Actual normalized original relation columns construct a feasible restricted
L² assignment, including every literal finite-pattern constraint. No initial
feasible assignment, recipient cover or positive atom-size bound is supplied. -/
theorem exists_normalized_assignment (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (hdisjoint : Pairwise (fun i j => Disjoint (I i) (I j))) :
    (∀ i, MeasurableSet (allowed μ Z I i)) ∧ Measurable (remainderSectionMass μ Z I) ∧
      ∃ q : ℕ → Lp ℝ 2 (μ.restrict (positiveSources μ Z)),
        ReverseAssignment.Feasible (allowed μ Z I) (remainderSectionMass μ Z I) q ∧
        (∀ i, (q i : Ω → ℝ) =ᵐ[μ.restrict (positiveSources μ Z)] rawFraction μ Z I i) ∧
        (∀ i, μ (I i) = 0 → (q i : Ω → ℝ) =ᵐ[μ.restrict (positiveSources μ Z)] 0) := by
  have hallowed := measurableSet_allowed (μ := μ) Z hZ I hI
  have hδ := measurable_remainderSectionMass (μ := μ) Z hZ I hI
  have hmem (i : ℕ) : MemLp (rawFraction μ Z I i) 2 (μ.restrict (positiveSources μ Z)) := by
    apply MemLp.of_bound (measurable_rawFraction (μ := μ) Z hZ I hI i).aestronglyMeasurable 1
    exact Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (rawFraction_box Z I i y).1]
      exact (rawFraction_box Z I i y).2)
  let q : ℕ → Lp ℝ 2 (μ.restrict (positiveSources μ Z)) :=
    fun i => (hmem i).toLp (rawFraction μ Z I i)
  have hcoe (i : ℕ) : (q i : Ω → ℝ) =ᵐ[μ.restrict (positiveSources μ Z)]
      rawFraction μ Z I i := (hmem i).coeFn_toLp
  have hcommon : ∀ᵐ y ∂μ.restrict (positiveSources μ Z),
      ∀ i, q i y = rawFraction μ Z I i y := ae_all_iff.mpr hcoe
  have hfeasible : ReverseAssignment.Feasible (allowed μ Z I) (remainderSectionMass μ Z I) q := by
    constructor
    · intro i
      filter_upwards [hcoe i] with y hy
      rw [hy]
      exact rawFraction_box Z I i y
    · intro i
      filter_upwards [hcoe i] with y hy hnot
      rw [hy]
      exact rawFraction_zero_of_notMem Z I i y hnot
    · intro J
      filter_upwards [hcommon] with y hy
      rw [Finset.sum_congr rfl (fun i _ => hy i)]
      exact rawFraction_partial_sum Z hZ I hI hdisjoint J y
    · intro J
      have hpattern := ReverseAssignment.measurableSet_finitePattern hallowed hδ J
      have hsource : ∀ᵐ y ∂μ.restrict (positiveSources μ Z), y ∈ positiveSources μ Z :=
        ae_restrict_mem (measurableSet_positiveSources Z hZ)
      filter_upwards [ae_restrict_of_ae hcommon, ae_restrict_of_ae hsource,
        ae_restrict_mem hpattern] with y hy hyH hyJ
      rw [Finset.sum_congr rfl (fun i _ => hy i)]
      exact rawFraction_full_pattern Z hZ I hI hdisjoint J y hyH hyJ
  refine ⟨hallowed, hδ, q, hfeasible, hcoe, ?_⟩
  intro i hi
  filter_upwards [hcoe i] with y hy
  rw [hy]
  exact rawFraction_zero_of_null Z I i hi y

end Erdos1017.MissingFlow.NormalizedAtomicFractions
