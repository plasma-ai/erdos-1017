module

public import Erdos1017.SelectedModel.Structure.CanonicalZeroGeometry
public import Erdos1017.SelectedModel.Structure.OrderedZeroBipartition

/-!
# Canonical zero relation and its left-side cut

The canonical zero relation on the common good-point set is measurable and
symmetric, its strict sections depend only on the row value, and the explicit
left-side cut is constant on each good whole row fiber and crosses distinct-row
canonical zero pairs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

universe u v

variable {Ω ι : Type u} {A : Type v}

/-- The canonical zero relation restricted to the common good-point set. -/
def canonicalZeroRelation (ν σ : ℝ) (φ : Ω → ℝ)
    (V : Ω → lp (fun _ : ι => ℝ) 2) (S : Set Ω) : Set (Ω × Ω) :=
  (S ×ˢ S) ∩ {p | canonicalPairing ν σ φ V p.1 p.2 = 0}

variable (ν σ : ℝ) (φ : Ω → ℝ) (V : Ω → lp (fun _ : ι => ℝ) 2) (S : Set Ω)

/-- Equal whole-row values give identical outgoing and incoming strict zero
sections at good points, including their actual physical locations. -/
theorem strict_neighbor_sections_eq_of_row_eq (ρ : Ω → A)
    (hcoords : ∀ x ∈ S, ∀ y ∈ S, ρ x = ρ y → φ x = φ y ∧ V x = V y)
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ S) (heq : ρ x = ρ y) :
    {z | (x, z) ∈ canonicalZeroRelation ν σ φ V S ∧ φ x < φ z} =
      {z | (y, z) ∈ canonicalZeroRelation ν σ φ V S ∧ φ y < φ z} ∧
    {z | (z, x) ∈ canonicalZeroRelation ν σ φ V S ∧ φ z < φ x} =
      {z | (z, y) ∈ canonicalZeroRelation ν σ φ V S ∧ φ z < φ y} := by
  obtain ⟨hφ, hV⟩ := hcoords x hx y hy heq
  constructor <;> ext z <;>
    simp only [canonicalZeroRelation, mem_inter_iff, mem_prod, mem_ofPred_eq,
      canonicalPairing, hx, hy, true_and, and_true, hφ, hV]

/-- The displayed canonical relation gives the actual strict right section
at every good point. -/
theorem rightNeighborMass_canonicalZeroRelation [MeasurableSpace Ω] (μ : Measure Ω)
    {x : Ω} (hx : x ∈ S) :
    OrderedZeroRelation.rightNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ x =
      μ {y | y ∈ S ∧ φ x < φ y ∧ canonicalPairing ν σ φ V x y = 0} := by
  apply congrArg μ
  ext y
  simp only [canonicalZeroRelation, mem_inter_iff, mem_prod, mem_ofPred_eq, hx, true_and]
  tauto

/-- The analogous incoming section retains the opposite strict order. -/
theorem leftNeighborMass_canonicalZeroRelation [MeasurableSpace Ω] (μ : Measure Ω)
    {y : Ω} (hy : y ∈ S) :
    OrderedZeroRelation.leftNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ y =
      μ {x | x ∈ S ∧ φ x < φ y ∧ canonicalPairing ν σ φ V x y = 0} := by
  apply congrArg μ
  ext x
  simp only [canonicalZeroRelation, mem_inter_iff, mem_prod, mem_ofPred_eq, hy, and_true]
  tauto

/-- The actual left and right section masses depend only on the supplied
row value on the common good-point set. -/
theorem neighbor_masses_eq_of_row_eq [MeasurableSpace Ω] (μ : Measure Ω) (ρ : Ω → A)
    (hcoords : ∀ x ∈ S, ∀ y ∈ S, ρ x = ρ y → φ x = φ y ∧ V x = V y)
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ S) (heq : ρ x = ρ y) :
    OrderedZeroRelation.rightNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ x =
      OrderedZeroRelation.rightNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ y ∧
    OrderedZeroRelation.leftNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ x =
      OrderedZeroRelation.leftNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ y := by
  have hs := strict_neighbor_sections_eq_of_row_eq ν σ φ V S ρ hcoords hx hy heq
  exact ⟨congrArg μ hs.1, congrArg μ hs.2⟩

/-- The explicitly defined left-side cut is constant on each good whole row
fiber, including fibers with no strict neighbors. -/
theorem leftSide_mem_iff_of_row_eq [MeasurableSpace Ω] (μ : Measure Ω) (ρ : Ω → A)
    (hcoords : ∀ x ∈ S, ∀ y ∈ S, ρ x = ρ y → φ x = φ y ∧ V x = V y)
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ S) (heq : ρ x = ρ y) :
    x ∈ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ ↔
      y ∈ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ := by
  change (0 < OrderedZeroRelation.rightNeighborMass μ _ φ x) ↔
    (0 < OrderedZeroRelation.rightNeighborMass μ _ φ y)
  rw [(neighbor_masses_eq_of_row_eq ν σ φ V S μ ρ hcoords hx hy heq).1]

/-- A positive whole fiber has a genuine common-good point. Its identical
strict sections place almost every point of the whole fiber on one side of
the explicit cut. -/
theorem positive_fiber_one_side [MeasurableSpace Ω] (μ : Measure Ω)
    (hSae : ∀ᵐ x ∂μ, x ∈ S) (ρ : Ω → A)
    (hcoords : ∀ x ∈ S, ∀ y ∈ S, ρ x = ρ y → φ x = φ y ∧ V x = V y)
    (r : A) (hmeas : MeasurableSet {x | ρ x = r}) (hpos : 0 < μ {x | ρ x = r}) :
    (∀ᵐ x ∂μ.restrict {x | ρ x = r},
      x ∈ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ) ∨
    (∀ᵐ x ∂μ.restrict {x | ρ x = r},
      x ∉ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ) := by
  obtain ⟨x, hxr, hxS⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (ae_restrict_of_ae hSae)
  have hgood : ∀ᵐ y ∂μ.restrict {x | ρ x = r}, y ∈ S ∧ ρ y = r :=
    (ae_restrict_of_ae hSae).and (ae_restrict_mem hmeas)
  by_cases hx : x ∈ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ
  · left
    filter_upwards [hgood] with y hy
    exact (leftSide_mem_iff_of_row_eq ν σ φ V S μ ρ hcoords hy.1 hxS
      (hy.2.trans hxr.symm)).mpr hx
  · right
    filter_upwards [hgood] with y hy
    exact fun hycut => hx ((leftSide_mem_iff_of_row_eq ν σ φ V S μ ρ hcoords hy.1 hxS
      (hy.2.trans hxr.symm)).mp hycut)

variable [MeasurableSpace Ω]

/-- The actual canonical zero relation is measurable. -/
theorem measurableSet_canonicalZeroRelation (hS : MeasurableSet S)
    (hφ : StronglyMeasurable φ) (hV : StronglyMeasurable V) :
    MeasurableSet (canonicalZeroRelation ν σ φ V S) := by
  have hpair : StronglyMeasurable (fun p : Ω × Ω => canonicalPairing ν σ φ V p.1 p.2) := by
    unfold canonicalPairing
    fun_prop
  exact (hS.prod hS).inter (measurableSet_eq_fun hpair.measurable measurable_const)

omit [MeasurableSpace Ω] in
/-- Symmetry here is pointwise for the displayed canonical relation, not a
pointwise assertion about the original kernel's exceptional representatives. -/
theorem canonicalZeroRelation_swap (p : Ω × Ω) :
    p ∈ canonicalZeroRelation ν σ φ V S ↔ p.swap ∈ canonicalZeroRelation ν σ φ V S := by
  have heq : canonicalPairing ν σ φ V p.2 p.1 = canonicalPairing ν σ φ V p.1 p.2 := by
    unfold canonicalPairing
    rw [real_inner_comm (V p.1) (V p.2)]
    ring
  change ((p.1 ∈ S ∧ p.2 ∈ S) ∧ canonicalPairing ν σ φ V p.1 p.2 = 0) ↔
    ((p.2 ∈ S ∧ p.1 ∈ S) ∧ canonicalPairing ν σ φ V p.2 p.1 = 0)
  rw [heq]
  tauto

/-- The explicit left-side cut crosses distinct-row canonical zero pairs.
The section-null calculation and unequal-coordinate crossing are consumed
from the ordered relation theorems. -/
theorem ae_distinct_row_zero_crosses_leftSide (μ : Measure Ω) [IsFiniteMeasure μ]
    (hS : MeasurableSet S) (hφ : StronglyMeasurable φ) (hV : StronglyMeasurable V)
    (ρ : Ω → A)
    (hnoMiddle : ∀ᵐ x ∂μ,
      OrderedZeroRelation.leftNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ x = 0 ∨
      OrderedZeroRelation.rightNeighborMass μ (canonicalZeroRelation ν σ φ V S) φ x = 0)
    (hequal : ∀ᵐ p ∂μ.prod μ, p ∈ canonicalZeroRelation ν σ φ V S →
      φ p.1 = φ p.2 → ρ p.1 = ρ p.2) :
    ∀ᵐ p ∂μ.prod μ, p ∈ canonicalZeroRelation ν σ φ V S → ρ p.1 ≠ ρ p.2 →
      (p.1 ∈ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ ∧
        p.2 ∉ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ) ∨
      (p.2 ∈ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ ∧
        p.1 ∉ OrderedZeroRelation.leftSide μ (canonicalZeroRelation ν σ φ V S) φ) := by
  let Z := canonicalZeroRelation ν σ φ V S
  have hZ := measurableSet_canonicalZeroRelation ν σ φ V S hS hφ hV
  have hsym : ∀ᵐ p ∂μ.prod μ, p ∈ Z ↔ p.swap ∈ Z :=
    Filter.Eventually.of_forall (canonicalZeroRelation_swap ν σ φ V S)
  have hnull := OrderedZeroRelation.side_intersection_null Z φ hnoMiddle
  have hnot : ∀ᵐ x ∂μ, x ∉ OrderedZeroRelation.leftSide μ Z φ ∩
      OrderedZeroRelation.rightSide μ Z φ := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [OrderedZeroRelation.ae_unequal_pair_crosses Z hZ φ hφ.measurable hsym,
    hequal, Measure.quasiMeasurePreserving_fst.ae hnot,
    Measure.quasiMeasurePreserving_snd.ae hnot] with p hp he hx hy hpZ hne
  have hφne : φ p.1 ≠ φ p.2 := fun heq => hne (he hpZ heq)
  rcases hp hpZ hφne with hf | hr
  · exact Or.inl ⟨hf.1, fun hmem => hy ⟨hmem, hf.2⟩⟩
  · exact Or.inr ⟨hr.1, fun hmem => hx ⟨hmem, hr.2⟩⟩

end Erdos1017.KernelOperator
