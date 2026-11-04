module

public import Erdos1017.SelectedModel.Flows.NormalizedRelationFlow
public import Erdos1017.SelectedModel.Structure.HighLowRelationClassification

/-!
# Forward and reverse relations by degree class

The forward and reverse relations receive at the higher- and lower-degree
endpoint respectively, so their full flows are supplied by the low and high
classes almost everywhere, and each constructed endpoint removes exactly its
supplied class.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Forward receipt is at the higher-degree endpoint of the original relation. -/
def forwardRelation (Z : Set (Ω × Ω)) (g : Ω → ℝ) : Set (Ω × Ω) :=
  {p | p.swap ∈ Z ∧ g p.2 < g p.1}

/-- Reverse receipt is at the lower-degree endpoint of the original relation. -/
def reverseRelation (Z : Set (Ω × Ω)) (g : Ω → ℝ) : Set (Ω × Ω) :=
  {p | p ∈ Z ∧ g p.1 < g p.2}

/-- Both original oriented relations are measurable. -/
theorem measurableSet_oriented_relations (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z)
    (g : Ω → ℝ) (hg : Measurable g) :
    MeasurableSet (forwardRelation Z g) ∧ MeasurableSet (reverseRelation Z g) := by
  exact ⟨(hZ.preimage measurable_swap).inter
    (measurableSet_lt (hg.comp measurable_snd) (hg.comp measurable_fst)),
    hZ.inter (measurableSet_lt (hg.comp measurable_fst) (hg.comp measurable_snd))⟩

/-- Forward positive sources are exactly the original strict upper-neighbor
side, before removal of its null intersection with HIGH. -/
theorem positiveSources_forwardRelation (Z : Set (Ω × Ω)) (g : Ω → ℝ) :
    positiveSources μ (forwardRelation Z g) = OrderedZeroRelation.leftSide μ Z g := by
  ext y
  change (0 < (μ {x | (y, x) ∈ Z ∧ g y < g x}).toReal) ↔
    0 < μ {x | (y, x) ∈ Z ∧ g y < g x}
  constructor
  · intro h
    apply pos_iff_ne_zero.mpr
    intro hz
    simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at h
  · intro h
    exact ENNReal.toReal_pos h.ne' (measure_ne_top μ _)

/-- Reverse positive sources are exactly HIGH, pointwise. -/
theorem positiveSources_reverseRelation (Z : Set (Ω × Ω)) (g : Ω → ℝ) :
    positiveSources μ (reverseRelation Z g) = OrderedZeroRelation.highClass μ Z g := by
  ext y
  change (0 < (μ {x | (x, y) ∈ Z ∧ g x < g y}).toReal) ↔
    0 < μ {x | (x, y) ∈ Z ∧ g x < g y}
  constructor
  · intro h
    apply pos_iff_ne_zero.mpr
    intro hz
    simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at h
  · intro h
    exact ENNReal.toReal_pos h.ne' (measure_ne_top μ _)

/-- The actual no-both-neighbors conclusion identifies full forward supply
with LOW almost everywhere, including its exceptional priority convention. -/
theorem ae_positiveSources_forward_eq_low (Z : Set (Ω × Ω)) (g : Ω → ℝ)
    (hnoBoth : ∀ᵐ x ∂μ, OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ Z g x = 0) :
    positiveSources μ (forwardRelation Z g) =ᵐ[μ] OrderedZeroRelation.lowClass μ Z g := by
  rw [positiveSources_forwardRelation]
  have hnull := OrderedZeroRelation.side_intersection_null Z g hnoBoth
  have hnot : ∀ᵐ x ∂μ,
      x ∉ OrderedZeroRelation.leftSide μ Z g ∩ OrderedZeroRelation.rightSide μ Z g := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hnot] with x hx
  apply propext
  change x ∈ OrderedZeroRelation.leftSide μ Z g ↔
    x ∈ OrderedZeroRelation.leftSide μ Z g ∧ x ∉ OrderedZeroRelation.rightSide μ Z g
  exact ⟨fun h => ⟨h, fun hr => hx ⟨h, hr⟩⟩, And.left⟩

/-- A product density supported in a recipient set has zero receipt outside
that set almost everywhere. The statement does not upgrade pair-AE support. -/
theorem ae_receipt_eq_zero_outside {q : Ω × Ω → ℝ} (R : Set Ω)
    (hR : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → p.1 ∈ R) :
    ∀ᵐ x ∂μ, x ∉ R → receipt μ q x = 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hR] with x hx hnot
  apply integral_eq_zero_of_ae
  filter_upwards [hx] with y hy
  by_contra hne
  exact hnot (hy hne)

/-- The actual degree classification places forward and reverse receipt
densities on HIGH and LOW respectively. -/
theorem ae_oriented_recipient_classes
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (g : Ω → ℝ) (hg : Measurable g)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hunequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → g p.1 ≠ g p.2)
    (hnoBoth : ∀ᵐ x ∂μ, OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ Z g x = 0) :
    (∀ᵐ p ∂μ.prod μ, normalizedDensity μ (forwardRelation Z g) p ≠ 0 →
      p.1 ∈ OrderedZeroRelation.highClass μ Z g) ∧
    (∀ᵐ p ∂μ.prod μ, normalizedDensity μ (reverseRelation Z g) p ≠ 0 →
      p.1 ∈ OrderedZeroRelation.lowClass μ Z g) := by
  have hcross := OrderedZeroRelation.ae_relation_crosses_high_low Z hZ g hg hsym hunequal hnoBoth
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcross
  constructor
  · filter_upwards [hswap] with p hp hne
    have hmem : p ∈ forwardRelation Z g := by
      by_contra hn
      exact hne (normalizedDensity_eq_zero_of_notMem _ _ hn)
    rcases hp hmem.1 with h | h
    · exact False.elim ((not_lt_of_ge hmem.2.le) h.2.2)
    · exact h.1
  · filter_upwards [hcross] with p hp hne
    have hmem : p ∈ reverseRelation Z g := by
      by_contra hn
      exact hne (normalizedDensity_eq_zero_of_notMem _ _ hn)
    rcases hp hmem.1 with h | h
    · exact False.elim ((not_lt_of_ge hmem.2.le) h.2.2)
    · exact h.2.1

/-- Both constructed full-flow endpoints remove exactly their supplied class
almost everywhere. No stationarity is assigned to either endpoint. -/
theorem ae_oriented_endpoints_remove_sources
    (Z : Set (Ω × Ω)) (hZ : MeasurableSet Z) (g : Ω → ℝ) (hg : Measurable g)
    (hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z)
    (hunequal : ∀ᵐ p ∂μ.prod μ, p ∈ Z → g p.1 ≠ g p.2)
    (hnoBoth : ∀ᵐ x ∂μ, OrderedZeroRelation.leftNeighborMass μ Z g x = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ Z g x = 0) :
    (∀ᵐ x ∂μ, x ∈ OrderedZeroRelation.lowClass μ Z g →
      1 + direction μ (normalizedDensity μ (forwardRelation Z g)) x = 0) ∧
    (∀ᵐ x ∂μ, x ∈ OrderedZeroRelation.highClass μ Z g →
      1 + direction μ (normalizedDensity μ (reverseRelation Z g)) x = 0) := by
  have hmeas := measurableSet_oriented_relations Z hZ g hg
  have hrec := ae_oriented_recipient_classes Z hZ g hg hsym hunequal hnoBoth
  have hdisjoint : Disjoint (OrderedZeroRelation.highClass μ Z g)
      (OrderedZeroRelation.lowClass μ Z g) :=
    (OrderedZeroRelation.measurable_high_low_neutral_partition Z hZ g hg).2.2.2.2.1
  constructor
  · filter_upwards [ae_receipt_eq_zero_outside _ hrec.1] with x hx hlow
    have hhigh : x ∉ OrderedZeroRelation.highClass μ Z g :=
      fun hh => Set.disjoint_left.mp hdisjoint hh hlow
    have hleft : x ∈ positiveSources μ (forwardRelation Z g) := by
      rw [positiveSources_forwardRelation]
      exact hlow.1
    dsimp only [direction]
    rw [hx hhigh, supply_normalizedDensity _ hmeas.1, indicator_of_mem hleft]
    ring
  · filter_upwards [ae_receipt_eq_zero_outside _ hrec.2] with x hx hhigh
    have hlow : x ∉ OrderedZeroRelation.lowClass μ Z g :=
      fun hl => Set.disjoint_left.mp hdisjoint hhigh hl
    have hsource : x ∈ positiveSources μ (reverseRelation Z g) := by
      rw [positiveSources_reverseRelation]
      exact hhigh
    dsimp only [direction]
    rw [hx hlow, supply_normalizedDensity _ hmeas.2, indicator_of_mem hsource]
    ring

end Erdos1017.MissingFlow
