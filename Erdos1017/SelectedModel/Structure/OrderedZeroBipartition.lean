module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Ordered sides of a symmetric zero relation

This module defines the strict left and right neighbor masses and sides of a
relation; almost every related pair with unequal scalar coordinates crosses the
two sides, so absence of middle points gives one measurable cut crossed by
almost every related pair of distinct rows.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Erdos1017.OrderedZeroRelation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual mass of strict right neighbors in the displayed relation. -/
def rightNeighborMass (μ : Measure Ω) (Z : Set (Ω × Ω)) (φ : Ω → ℝ) (x : Ω) : ℝ≥0∞ :=
  μ {y | (x, y) ∈ Z ∧ φ x < φ y}

/-- The actual mass of strict left neighbors in the displayed relation. -/
def leftNeighborMass (μ : Measure Ω) (Z : Set (Ω × Ω)) (φ : Ω → ℝ) (y : Ω) : ℝ≥0∞ :=
  μ {x | (x, y) ∈ Z ∧ φ x < φ y}

/-- The left side consists of points with positive strict right-neighbor mass. -/
def leftSide (μ : Measure Ω) (Z : Set (Ω × Ω)) (φ : Ω → ℝ) : Set Ω :=
  {x | 0 < rightNeighborMass μ Z φ x}

/-- The right side consists of points with positive strict left-neighbor mass. -/
def rightSide (μ : Measure Ω) (Z : Set (Ω × Ω)) (φ : Ω → ℝ) : Set Ω :=
  {y | 0 < leftNeighborMass μ Z φ y}

variable [IsFiniteMeasure μ]

/-- Joint measurability gives measurability of actual strict section masses. -/
theorem measurable_rightNeighborMass (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (φ : Ω → ℝ) (hφ : Measurable φ) : Measurable (rightNeighborMass μ Z φ) := by
  exact measurable_measure_prodMk_left (ν := μ)
    (hZ.inter (measurableSet_lt (hφ.comp measurable_fst) (hφ.comp measurable_snd)))

/-- The incoming strict section mass is measurable as well. -/
theorem measurable_leftNeighborMass (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (φ : Ω → ℝ) (hφ : Measurable φ) : Measurable (leftNeighborMass μ Z φ) := by
  exact measurable_measure_prodMk_right (μ := μ)
    (hZ.inter (measurableSet_lt (hφ.comp measurable_fst) (hφ.comp measurable_snd)))

theorem measurableSet_leftSide (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (φ : Ω → ℝ) (hφ : Measurable φ) : MeasurableSet (leftSide μ Z φ) :=
  measurableSet_lt measurable_const (measurable_rightNeighborMass (μ := μ) Z hZ φ hφ)

theorem measurableSet_rightSide (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (φ : Ω → ℝ) (hφ : Measurable φ) : MeasurableSet (rightSide μ Z φ) :=
  measurableSet_lt measurable_const (measurable_leftNeighborMass (μ := μ) Z hZ φ hφ)

private theorem ae_mem_positive_section (T : Set (Ω × Ω)) (hT : MeasurableSet T) :
    ∀ᵐ p ∂μ.prod μ, p ∈ T → 0 < μ (Prod.mk p.1 ⁻¹' T) := by
  let A := {p : Ω × Ω | p ∈ T ∧ μ (Prod.mk p.1 ⁻¹' T) = 0}
  have hmass : Measurable (fun p : Ω × Ω => μ (Prod.mk p.1 ⁻¹' T)) :=
    (measurable_measure_prodMk_left (ν := μ) hT).comp measurable_fst
  have hA : MeasurableSet A := hT.inter (measurableSet_eq_fun hmass measurable_const)
  have hnull : (μ.prod μ) A = 0 := by
    apply Measure.measure_prod_null_of_ae_null hA
    filter_upwards with x
    change μ (Prod.mk x ⁻¹' A) = 0
    by_cases hx : μ (Prod.mk x ⁻¹' T) = 0
    · apply measure_mono_null _ hx
      intro y hy
      exact hy.1
    · have heq : Prod.mk x ⁻¹' A = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun _ hy => hx hy.2)
      rw [heq, measure_empty]
  have hnot : ∀ᵐ p ∂μ.prod μ, p ∉ A := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hnot] with p hp hpt
  exact pos_iff_ne_zero.mpr (fun hz => hp ⟨hpt, hz⟩)

/-- Almost every strict increasing pair has positive sections at both ends.
Zero-mass sections are discarded by the derived product-null calculation. -/
theorem ae_increasing_pair_crosses (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (φ : Ω → ℝ) (hφ : Measurable φ) :
    ∀ᵐ p ∂μ.prod μ, p ∈ Z → φ p.1 < φ p.2 →
      p.1 ∈ leftSide μ Z φ ∧ p.2 ∈ rightSide μ Z φ := by
  let T := Z ∩ {p : Ω × Ω | φ p.1 < φ p.2}
  have hT : MeasurableSet T :=
    hZ.inter (measurableSet_lt (hφ.comp measurable_fst) (hφ.comp measurable_snd))
  have hout := ae_mem_positive_section (μ := μ) T hT
  have hin := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (ae_mem_positive_section (μ := μ) (Prod.swap ⁻¹' T) (hT.preimage measurable_swap))
  filter_upwards [hout, hin] with p hp hq hpZ horder
  have hpT : p ∈ T := ⟨hpZ, horder⟩
  exact ⟨hp hpT, hq hpT⟩

/-- An almost-everywhere symmetric relation crosses the two ordered sides
at almost every related pair with unequal scalar coordinates. -/
theorem ae_unequal_pair_crosses (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (φ : Ω → ℝ) (hφ : Measurable φ)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z) :
    ∀ᵐ p ∂μ.prod μ, p ∈ Z → φ p.1 ≠ φ p.2 →
      (p.1 ∈ leftSide μ Z φ ∧ p.2 ∈ rightSide μ Z φ) ∨
      (p.2 ∈ leftSide μ Z φ ∧ p.1 ∈ rightSide μ Z φ) := by
  have hforward := ae_increasing_pair_crosses (μ := μ) Z hZ φ hφ
  have hreverse := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hforward
  filter_upwards [hforward, hreverse, hsym] with p hp hq hs hpZ hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl (hp hpZ hlt)
  · exact Or.inr (hq (hs.mp hpZ) hgt)

omit [IsFiniteMeasure μ] in
/-- Absence of two positive strict neighborhoods makes the displayed sides
almost everywhere disjoint, for their actual section-mass definitions. -/
theorem side_intersection_null (Z : Set (Ω × Ω)) (φ : Ω → ℝ)
    (hnoMiddle : ∀ᵐ x ∂μ, leftNeighborMass μ Z φ x = 0 ∨ rightNeighborMass μ Z φ x = 0) :
    μ (leftSide μ Z φ ∩ rightSide μ Z φ) = 0 := by
  have hnot : ∀ᵐ x ∂μ, x ∉ leftSide μ Z φ ∩ rightSide μ Z φ := by
    filter_upwards [hnoMiddle] with x hx hmem
    rcases hx with hl | hr
    · exact (ne_of_gt hmem.2) hl
    · exact (ne_of_gt hmem.1) hr
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnot

/-- No middle point and the equal-coordinate row identity give one actual
measurable cut crossed by almost every related pair of distinct rows. -/
theorem exists_measurable_cut_of_ae_no_middle {A : Type*}
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (φ : Ω → ℝ) (hφ : Measurable φ)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hnoMiddle : ∀ᵐ x ∂μ, leftNeighborMass μ Z φ x = 0 ∨ rightNeighborMass μ Z φ x = 0)
    (ρ : Ω → A) (hequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → φ p.1 = φ p.2 → ρ p.1 = ρ p.2) :
    ∃ B : Set Ω, MeasurableSet B ∧
      ∀ᵐ p ∂μ.prod μ, p ∈ Z → ρ p.1 ≠ ρ p.2 →
        (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B) := by
  have hnull := side_intersection_null Z φ hnoMiddle
  have hnot : ∀ᵐ x ∂μ, x ∉ leftSide μ Z φ ∩ rightSide μ Z φ := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  refine ⟨leftSide μ Z φ, measurableSet_leftSide Z hZ φ hφ, ?_⟩
  filter_upwards [ae_unequal_pair_crosses Z hZ φ hφ hsym, hequal,
    Measure.quasiMeasurePreserving_fst.ae hnot,
    Measure.quasiMeasurePreserving_snd.ae hnot] with p hp he hx hy hpZ hne
  have hφne : φ p.1 ≠ φ p.2 := fun hφeq => hne (he hpZ hφeq)
  rcases hp hpZ hφne with hforward | hreverse
  · exact Or.inl ⟨hforward.1, fun hmem => hy ⟨hmem, hforward.2⟩⟩
  · exact Or.inr ⟨hreverse.1, fun hmem => hx ⟨hmem, hreverse.2⟩⟩

/-- If related pairs in a measurable remainder always have distinct rows,
both pieces of the derived measurable cut have zero-free internal pairs. -/
theorem exists_measurable_cut_zero_free_on {A : Type*}
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (φ : Ω → ℝ) (hφ : Measurable φ)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hnoMiddle : ∀ᵐ x ∂μ, leftNeighborMass μ Z φ x = 0 ∨ rightNeighborMass μ Z φ x = 0)
    (ρ : Ω → A) (hequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → φ p.1 = φ p.2 → ρ p.1 = ρ p.2)
    (D : Set Ω) (hD : MeasurableSet D)
    (hdistinct : ∀ᵐ p ∂μ.prod μ, p ∈ Z → p.1 ∈ D → p.2 ∈ D → ρ p.1 ≠ ρ p.2) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ᵐ p ∂μ.prod μ, p ∈ Z → ρ p.1 ≠ ρ p.2 →
        (p.1 ∈ B ∧ p.2 ∉ B) ∨ (p.2 ∈ B ∧ p.1 ∉ B)) ∧
      (∀ᵐ p ∂(μ.restrict (D ∩ B)).prod (μ.restrict (D ∩ B)), p ∉ Z) ∧
      (∀ᵐ p ∂(μ.restrict (D \ B)).prod (μ.restrict (D \ B)), p ∉ Z) := by
  obtain ⟨B, hB, hcross⟩ := exists_measurable_cut_of_ae_no_middle
    Z hZ φ hφ hsym hnoMiddle ρ hequal
  refine ⟨B, hB, hcross, ?_, ?_⟩
  · rw [Measure.prod_restrict]
    apply (ae_restrict_iff' ((hD.inter hB).prod (hD.inter hB))).mpr
    filter_upwards [hcross, hdistinct] with p hp hd hmem hpZ
    have hrow := hd hpZ hmem.1.1 hmem.2.1
    rcases hp hpZ hrow with hforward | hreverse
    · exact hforward.2 hmem.2.2
    · exact hreverse.2 hmem.1.2
  · rw [Measure.prod_restrict]
    apply (ae_restrict_iff' ((hD.diff hB).prod (hD.diff hB))).mpr
    filter_upwards [hcross, hdistinct] with p hp hd hmem hpZ
    have hrow := hd hpZ hmem.1.1 hmem.2.1
    rcases hp hpZ hrow with hforward | hreverse
    · exact hmem.1.2 hforward.1
    · exact hmem.2.2 hreverse.1

end Erdos1017.OrderedZeroRelation
