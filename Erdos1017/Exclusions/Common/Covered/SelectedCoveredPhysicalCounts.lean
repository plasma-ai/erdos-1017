module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredAveraging
public import Erdos1017.Exclusions.Common.Physical.PhysicalConditionalAveraging

/-!
# Tight physical primal for the covered average

The unchanged singular primal is tight for the countable averaged dual, and the
selected model constructs a bounded-order primal with the exact original cost,
root leaves, unique-root coverage and tightness
(`exists_covered_tight_physical_primal`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- The unchanged original singular primal is tight for the literal
countable averaged dual. Its genuine pair balance licenses the label
graph, and independent conditional tests supply pointwise feasibility. -/
theorem UniversalPhysicalPrimal.ae_tight_covered_average
    {S : SelectedHighLowStructure W m} {r : S.I} {d c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (a : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, PhysicalPrimal.charge
      (Function.uncurry (ConditionalAveraging.charge (μ := μ)
        (S.coveredLabel a) (chargeKernel W))) v = 1 := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hgraph : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) := by
    filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs] with p hg hp
    change W.moment CappedColor.adjacency p = _ at hg
    have he := hp.symm.trans hg
    cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
      cases hH : S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) <;>
      simp_all [A]
  have hcost : PhysicalPrimal.cost P.laws = (∫ p, Y p.1 p.2 ∂μ.prod μ) / 2 := by
    rw [P.cost, ← hW.objective_eq]
    unfold objective
    congr 1
    exact integral_congr_ae ((PhysicalRepresentative.charge_ae_eq W m hs).mono (fun _ hp => hp.symm))
  have ht := PhysicalPrimal.ae_tight_conditional_average P.laws A
    (PhysicalRepresentative.measurable_adjacency W m)
    (S.coveredLabel a) (S.measurable_coveredLabel a) (S.coveredLabel_fibers_positive a hR hE)
    (S.coveredGraph r a) hgraph Y (PhysicalRepresentative.measurable_charge W m)
    (PhysicalRepresentative.charge_mem_Icc W m) (PhysicalRepresentative.charge_zero_of_nonedge W m)
    (PhysicalRepresentative.full_feasible W hW.full m hs hW.deterministic) P.feasible hcost n
  have heq : Function.uncurry (ConditionalAveraging.charge (μ := μ) (S.coveredLabel a) Y) =
      Function.uncurry (ConditionalAveraging.charge (μ := μ) (S.coveredLabel a) (chargeKernel W)) := by
    funext p
    exact ConditionalAveraging.charge_congr_ae (S.coveredLabel a) Y (chargeKernel W)
      (PhysicalRepresentative.charge_ae_eq W m hs) p.1 p.2
  rwa [heq] at ht

/-- The same selected model constructs the actual bounded-order primal
internally, with exact old cost and root leaves, unique-root coverage,
and tightness for the entire countable averaged entry dual. -/
theorem exists_covered_tight_physical_primal
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) :
    ∃ P : S.UniversalPhysicalPrimal r c,
      (∀ n, ∀ᵐ v ∂P.laws n, ∃! i, S.ρ (v i) = r.val) ∧
      (∀ n, PhysicalRootReplacement.noRootLaw (P.laws n) {x | S.ρ x = r.val} = 0) ∧
      ∀ n, ∀ᵐ v ∂P.laws n, PhysicalPrimal.charge
        (Function.uncurry (ConditionalAveraging.charge (μ := μ)
          (S.coveredLabel a) (chargeKernel W))) v = 1 := by
  obtain ⟨P, hroot, hnoRoot⟩ := S.exists_rooted_primal_of_zero_body r hW hd hgap hzero
  exact ⟨P, hroot, hnoRoot,
    P.ae_tight_covered_average a hW hd hgap hpair hzero hR hE⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
