module

public import Erdos1017.SelectedModel.Structure.OrderedZeroBipartition

/-!
# High, low and neutral classes of a relation

High vertices have positive mass of strictly lower relation neighbors, low
vertices have strictly upper neighbors, and neutral is the remainder; the three
classes form a measurable partition, almost every related pair crosses from high
to low, and neutral vertices have null relation sections.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1017.OrderedZeroRelation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- HIGH vertices have positive mass of strictly lower relation neighbors. -/
def highClass (μ : Measure Ω) (Z : Set (Ω × Ω)) (g : Ω → ℝ) : Set Ω :=
  rightSide μ Z g

/-- LOW vertices have strictly upper neighbors; HIGH has priority on the
exceptional intersection, making the displayed partition pointwise disjoint. -/
def lowClass (μ : Measure Ω) (Z : Set (Ω × Ω)) (g : Ω → ℝ) : Set Ω :=
  leftSide μ Z g \ highClass μ Z g

/-- NEUTRAL is the remainder of the two explicitly displayed classes. -/
def neutralClass (μ : Measure Ω) (Z : Set (Ω × Ω)) (g : Ω → ℝ) : Set Ω :=
  (highClass μ Z g ∪ lowClass μ Z g)ᶜ

variable [IsFiniteMeasure μ]

/-- The three measured classes form an actual pointwise partition. -/
theorem measurable_high_low_neutral_partition
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (g : Ω → ℝ) (hg : Measurable g) :
    MeasurableSet (highClass μ Z g) ∧ MeasurableSet (lowClass μ Z g) ∧
      MeasurableSet (neutralClass μ Z g) ∧
      highClass μ Z g ∪ lowClass μ Z g ∪ neutralClass μ Z g = univ ∧
      Disjoint (highClass μ Z g) (lowClass μ Z g) ∧
      Disjoint (highClass μ Z g) (neutralClass μ Z g) ∧
      Disjoint (lowClass μ Z g) (neutralClass μ Z g) := by
  have hH : MeasurableSet (highClass μ Z g) := measurableSet_rightSide Z hZ g hg
  have hL : MeasurableSet (lowClass μ Z g) := (measurableSet_leftSide Z hZ g hg).diff hH
  refine ⟨hH, hL, (hH.union hL).compl, union_compl_self _, ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  · exact Set.disjoint_left.mpr (fun _ hx hy => hy (Or.inl hx))
  · exact Set.disjoint_left.mpr (fun _ hx hy => hy (Or.inr hx))

/-- Almost every related pair crosses HIGH to LOW, with strictly larger
original scalar degree at the HIGH endpoint. The original ordered section
core supplies all positive-section and null-intersection facts. -/
theorem ae_relation_crosses_high_low
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (g : Ω → ℝ) (hg : Measurable g)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hunequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → g p.1 ≠ g p.2)
    (hnoBoth : ∀ᵐ x ∂μ, leftNeighborMass μ Z g x = 0 ∨ rightNeighborMass μ Z g x = 0) :
    ∀ᵐ p ∂μ.prod μ, p ∈ Z →
      (p.1 ∈ highClass μ Z g ∧ p.2 ∈ lowClass μ Z g ∧ g p.2 < g p.1) ∨
      (p.2 ∈ highClass μ Z g ∧ p.1 ∈ lowClass μ Z g ∧ g p.1 < g p.2) := by
  have hnull := side_intersection_null Z g hnoBoth
  have hnot : ∀ᵐ x ∂μ, x ∉ leftSide μ Z g ∩ rightSide μ Z g := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  have hinc := ae_increasing_pair_crosses (μ := μ) Z hZ g hg
  have hdec := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hinc
  filter_upwards [ae_unequal_pair_crosses Z hZ g hg hsym, hinc, hdec, hsym, hunequal,
    Measure.quasiMeasurePreserving_fst.ae hnot,
    Measure.quasiMeasurePreserving_snd.ae hnot] with p hp hi hd hs hn hx hy hpZ
  have hne := hn hpZ
  rcases hp hpZ hne with hf | hr
  · have hlt : g p.1 < g p.2 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · exact False.elim (hx ⟨hf.1, (hd (hs.mp hpZ) h).2⟩)
    exact Or.inr ⟨hf.2, ⟨hf.1, fun h => hx ⟨hf.1, h⟩⟩, hlt⟩
  · have hlt : g p.2 < g p.1 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact False.elim (hy ⟨hr.1, (hi hpZ h).2⟩)
      · exact h
    exact Or.inl ⟨hr.2, ⟨hr.1, fun h => hy ⟨hr.1, h⟩⟩, hlt⟩

/-- Neutral vertices have zero mass of actual relation neighbors almost
everywhere. This follows from the derived crossing, not a supplied section
nullity or an additional Tonelli argument. -/
theorem ae_neutral_section_null
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (g : Ω → ℝ) (hg : Measurable g)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hunequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → g p.1 ≠ g p.2)
    (hnoBoth : ∀ᵐ x ∂μ, leftNeighborMass μ Z g x = 0 ∨ rightNeighborMass μ Z g x = 0) :
    ∀ᵐ x ∂μ, x ∈ neutralClass μ Z g → μ {y | (x, y) ∈ Z} = 0 := by
  have hsections := Measure.ae_ae_of_ae_prod
    (ae_relation_crosses_high_low Z hZ g hg hsym hunequal hnoBoth)
  filter_upwards [hsections] with x hx hneutral
  have hnone : ∀ᵐ y ∂μ, (x, y) ∉ Z := by
    filter_upwards [hx] with y hy hxy
    rcases hy hxy with h | h
    · exact hneutral (Or.inl h.1)
    · exact hneutral (Or.inr h.2.1)
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnone

/-- Actual homogeneous degree and relation sections determine one class on
a supplied set almost everywhere. The class is derived from the section
masses; no class assignment for a whole fiber is assumed. -/
theorem ae_one_class_of_homogeneous_sections
    (Z : Set (Ω × Ω)) (g : Ω → ℝ)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (I T : Set Ω) (a : ℝ) (hdegree : g =ᵐ[μ.restrict I] fun _ => a)
    (hsections : ∀ᵐ x ∂μ.restrict I, ∀ᵐ y ∂μ, (x, y) ∈ Z ↔ y ∈ T) :
    (∀ᵐ x ∂μ.restrict I, x ∈ highClass μ Z g) ∨
      (∀ᵐ x ∂μ.restrict I, x ∈ lowClass μ Z g) ∨
      (∀ᵐ x ∂μ.restrict I, x ∈ neutralClass μ Z g) := by
  have hmass : ∀ᵐ x ∂μ.restrict I,
      leftNeighborMass μ Z g x = μ (T ∩ {y | g y < a}) ∧
      rightNeighborMass μ Z g x = μ (T ∩ {y | a < g y}) := by
    filter_upwards [hdegree, hsections, ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hsym)]
      with x hx ht hs
    constructor
    · apply measure_congr
      filter_upwards [ht, hs] with y hy hxy
      apply propext
      change ((y, x) ∈ Z ∧ g y < g x) ↔ (y ∈ T ∧ g y < a)
      change (x, y) ∈ Z ↔ (y, x) ∈ Z at hxy
      rw [← hxy, hy, hx]
    · apply measure_congr
      filter_upwards [ht] with y hy
      apply propext
      change ((x, y) ∈ Z ∧ g x < g y) ↔ (y ∈ T ∧ a < g y)
      rw [hy, hx]
  by_cases hl : 0 < μ (T ∩ {y | g y < a})
  · left
    filter_upwards [hmass] with x hx
    change 0 < leftNeighborMass μ Z g x
    rwa [hx.1]
  · by_cases hu : 0 < μ (T ∩ {y | a < g y})
    · right
      left
      filter_upwards [hmass] with x hx
      refine ⟨?_, ?_⟩
      · change 0 < rightNeighborMass μ Z g x
        rwa [hx.2]
      · intro hh
        apply hl
        change 0 < leftNeighborMass μ Z g x at hh
        rwa [hx.1] at hh
    · right
      right
      filter_upwards [hmass] with x hx
      change x ∉ highClass μ Z g ∪ lowClass μ Z g
      rintro (hh | hh)
      · apply hl
        change 0 < leftNeighborMass μ Z g x at hh
        rwa [hx.1] at hh
      · apply hu
        have hp := hh.1
        change 0 < rightNeighborMass μ Z g x at hp
        rwa [hx.2] at hp

end Erdos1017.OrderedZeroRelation
