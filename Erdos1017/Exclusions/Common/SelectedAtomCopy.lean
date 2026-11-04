module

public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyReweight
public import Erdos1017.Exclusions.Common.SelectedRootRows

/-!
# Atom copy in the selected model

The selected root fiber is independent for the bounded symmetric physical graph,
copying a nonnegative adjacent source pair is fully scalar feasible at every
fresh mass, and the copied competitor, with any density-restoring reweighting on
the same source-pair event, is bounded by the full density limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual selected root fiber is independent for the bounded symmetric
physical graph, with one original product-null exception. -/
theorem ae_root_fiber_physical_independent (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
  filter_upwards [S.ae_root_adjacency r hW hd hgap] with p hp hx hy
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact ((hp hx).mp htrue).1 hy

/-- Copying an actual nonnegative adjacent old source pair gives full
scalar feasibility at every fresh mass. All source sections and old tests
are derived from the original selected model. -/
theorem ae_atom_copy_full_tests (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ,
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      0 ≤ PhysicalRepresentative.charge W m p.1 p.2 →
      ∀ t : unitInterval, ∀ n,
        FiniteArity.FeasibleOrder (universalMeasure μ t)
          (IndependentAtomCopy.markedAdjacency (PhysicalRepresentative.adjacency W m) p.1 p.2)
          (IndependentAtomCopy.markedCharge (PhysicalRepresentative.adjacency W m)
            (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} p.1 p.2) n := by
  exact IndependentAtomCopy.ae_all_marked_feasibleOrder
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val}
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_symm W m p.1 p.2))
    (S.ae_root_fiber_physical_independent r hW hd hgap)
    (PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic)

/-- The actual copied scalar competitor is bounded by the full density
limit, without imposing the old compact color charge box on its new row. -/
theorem ae_atom_copy_objective_le_densityLimit (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ,
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      0 ≤ PhysicalRepresentative.charge W m p.1 p.2 → ∀ t : unitInterval,
      FiniteCappedSamplingCost.physicalObjective (universalMeasure μ t)
          (IndependentAtomCopy.markedCharge (PhysicalRepresentative.adjacency W m)
            (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} p.1 p.2) ≤
        FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
          (universalMeasure μ t)
          (IndependentAtomCopy.markedAdjacency
            (PhysicalRepresentative.adjacency W m) p.1 p.2)) := by
  exact IndependentAtomCopy.ae_copy_objective_le_densityLimit
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.measurable_charge W m) (PhysicalRepresentative.charge_symm W m)
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 3 (by norm_num)
    (PhysicalRepresentative.charge_bound W m)
    (S.ae_root_fiber_physical_independent r hW hd hgap)
    (PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic)

/-- Actual density-restoring reweightings may all use this same original
source-pair event, including weights selected after the pair is known. -/
theorem ae_atom_copy_objective_le_densityLimit_ac (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ,
      PhysicalRepresentative.adjacency W m p.1 p.2 = true →
      0 ≤ PhysicalRepresentative.charge W m p.1 p.2 →
      ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ → ∀ t : unitInterval,
        FiniteCappedSamplingCost.physicalObjective (universalMeasure ν t)
            (IndependentAtomCopy.markedCharge (PhysicalRepresentative.adjacency W m)
              (PhysicalRepresentative.charge W m) {x | S.ρ x = r.val} p.1 p.2) ≤
          FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity
            (universalMeasure ν t)
            (IndependentAtomCopy.markedAdjacency
              (PhysicalRepresentative.adjacency W m) p.1 p.2)) := by
  exact IndependentAtomCopy.ae_copy_objective_le_densityLimit_ac
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.measurable_charge W m) (PhysicalRepresentative.charge_symm W m)
    {x | S.ρ x = r.val} (S.hfibers r.val r.property).1 3 (by norm_num)
    (PhysicalRepresentative.charge_bound W m)
    (S.ae_root_fiber_physical_independent r hW hd hgap)
    (PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic)

end Erdos1017.CappedModel.SelectedHighLowStructure
