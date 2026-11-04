module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTwoExteriorPartition
public import Erdos1017.Exclusions.Common.Covered.CoveredBoundaryCoefficientBounds
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorNeighborBlocks

/-!
# Finite partition for the covered two-neighbor boundary

The finite index `coveredTwoNeighborIndex` reuses the original
`A`/`B`/`C1`/`C2`/`D` coding and reindexes the countable label pointwise, and on
the `E`-null boundary the original model has the five-region neighbor graph
almost everywhere, with only the null `E` region removed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Reuse the literal original A/B/C1/C2/D finite coding. On the E-null
boundary D is R almost everywhere; its fifth fiber remains D exactly. -/
def coveredTwoNeighborIndex (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I) :
    Fin 5 → S.I ⊕ Unit := ![Sum.inl a, Sum.inl r, Sum.inl z1, Sum.inl z2, Sum.inr ()]

theorem coveredTwoNeighborIndex_fibers (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) (i : Fin 5) :
    S.coveredTwoBoundaryLabel r a z1 ⁻¹' {i} =
      S.coveredCountableBoundaryLabel ⁻¹' {S.coveredTwoNeighborIndex r a z1 z2 i} := by
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    S.coveredTwoBoundaryLabel_fibers r a z1 z2 hra hz1r hz1a hz2r hz2a hz12 hatoms
  fin_cases i
  · exact h0.trans (S.coveredCountableBoundaryLabel_fiber_inl a).symm
  · exact h1.trans (S.coveredCountableBoundaryLabel_fiber_inl r).symm
  · exact h2.trans (S.coveredCountableBoundaryLabel_fiber_inl z1).symm
  · exact h3.trans (S.coveredCountableBoundaryLabel_fiber_inl z2).symm
  · exact h4.trans S.coveredCountableBoundaryLabel_fiber_inr.symm

/-- The actual finite label reindexes the original countable label
pointwise, using the explicit four-atom exhaustion. -/
theorem coveredTwoNeighborIndex_label (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) (x : Ω) :
    S.coveredCountableBoundaryLabel x = S.coveredTwoNeighborIndex r a z1 z2
      (S.coveredTwoBoundaryLabel r a z1 x) := by
  have hx : x ∈ S.coveredTwoBoundaryLabel r a z1 ⁻¹' {S.coveredTwoBoundaryLabel r a z1 x} := rfl
  rw [S.coveredTwoNeighborIndex_fibers r a z1 z2 hra hz1r hz1a hz2r hz2a hz12 hatoms] at hx
  exact hx

/-- The E-null mode has A-R present and the exact neighbor table. -/
theorem coveredGraph_twoNeighborIndex (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2) (i j : Fin 5) :
    S.coveredCountableBoundaryGraph true r a (S.coveredTwoNeighborIndex r a z1 z2 i)
      (S.coveredTwoNeighborIndex r a z1 z2 j) = CoveredTwoExteriorNeighbor.blockAdjacency i j := by
  fin_cases i <;> fin_cases j <;>
    simp [coveredCountableBoundaryGraph, coveredBoundaryExpand, coveredGraph,
      coveredTwoNeighborIndex, CoveredTwoExteriorNeighbor.blockAdjacency,
      hra, hz1r, hz1a, hz2r, hz2a, hz12,
      Ne.symm hra, Ne.symm hz1r, Ne.symm hz1a, Ne.symm hz2r, Ne.symm hz2a, Ne.symm hz12]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The E-null original model has the actual five-region neighbor graph.
The only region removed by a null event is the explicitly null E region. -/
theorem ae_covered_two_neighbor_graph (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hE : μ (S.D \ S.rootNeighborhood a) = 0)
    (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a) (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if CoveredTwoExteriorNeighbor.blockAdjacency
        (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2) = true
      then 1 else 0 := by
  filter_upwards [S.ae_covered_countable_boundary_graph true r a hW hd hgap hpair hzero
    (by simpa using hE)] with p hp
  rw [S.coveredTwoNeighborIndex_label r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms p.1,
    S.coveredTwoNeighborIndex_label r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms p.2,
    S.coveredGraph_twoNeighborIndex r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12] at hp
  exact hp

end Erdos1017.CappedModel.SelectedHighLowStructure
