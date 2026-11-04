module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.Covered.CoveredTwoExteriorBlocks

/-!
# Boundary labeling for the two-exterior case

Defines the five-label boundary coding, which merges both diffuse regions into
the `D` fiber and orders the labels `A, B, C1, C2, E`, and its partial inverse,
exact away from the `R` region. If the `R` region is null, the coded graph
agrees almost everywhere with the original boundary graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Collapse both diffuse regions to the literal original D fiber.
The finite order is A, B, C1, C2, E. -/
def coveredTwoBoundaryCode (S : SelectedHighLowStructure W m) (r a z1 : S.I) : S.I ⊕ Bool → Fin 5
  | Sum.inl u => if u = a then 0 else if u = r then 1 else if u = z1 then 2 else 3
  | Sum.inr _ => 4

def coveredTwoBoundaryLabel (S : SelectedHighLowStructure W m) (r a z1 : S.I) (x : Ω) : Fin 5 :=
  S.coveredTwoBoundaryCode r a z1 (S.coveredLabel a x)

def coveredTwoBoundaryIndex (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I) :
    Fin 5 → S.I ⊕ Bool := ![Sum.inl a, Sum.inl r, Sum.inl z1, Sum.inl z2, Sum.inr false]

theorem measurable_coveredTwoBoundaryLabel (S : SelectedHighLowStructure W m) (r a z1 : S.I) :
    Measurable (S.coveredTwoBoundaryLabel r a z1) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable (S.coveredTwoBoundaryCode r a z1)).comp
    (S.measurable_coveredLabel a)

/-- The diffuse fiber is D exactly, even before the R-null assumption. -/
theorem coveredTwoBoundaryLabel_fibers (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {0}) = {x | S.ρ x = a.val} ∧
    (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {1}) = {x | S.ρ x = r.val} ∧
    (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {2}) = {x | S.ρ x = z1.val} ∧
    (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {3}) = {x | S.ρ x = z2.val} ∧
    (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {4}) = S.D := by
  have hc (i : S.I ⊕ Bool) :
      (S.coveredTwoBoundaryCode r a z1 i = 0 ↔ i = Sum.inl a) ∧
      (S.coveredTwoBoundaryCode r a z1 i = 1 ↔ i = Sum.inl r) ∧
      (S.coveredTwoBoundaryCode r a z1 i = 2 ↔ i = Sum.inl z1) ∧
      (S.coveredTwoBoundaryCode r a z1 i = 3 ↔ i = Sum.inl z2) ∧
      (S.coveredTwoBoundaryCode r a z1 i = 4 ↔ ∃ b, i = Sum.inr b) := by
    cases i with
    | inl u =>
      rcases hatoms u with rfl | rfl | rfl | rfl <;>
        simp [coveredTwoBoundaryCode, hra, hz1r, hz1a, hz2r, hz2a, hz12,
          Ne.symm hra, Ne.symm hz1r, Ne.symm hz1a, Ne.symm hz2r, Ne.symm hz2a, Ne.symm hz12]
    | inr b => simp [coveredTwoBoundaryCode]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    exact (hc (S.coveredLabel a x)).1.trans (S.coveredLabel_eq_inl_iff a a x)
  · ext x
    exact (hc (S.coveredLabel a x)).2.1.trans (S.coveredLabel_eq_inl_iff a r x)
  · ext x
    exact (hc (S.coveredLabel a x)).2.2.1.trans (S.coveredLabel_eq_inl_iff a z1 x)
  · ext x
    exact (hc (S.coveredLabel a x)).2.2.2.1.trans (S.coveredLabel_eq_inl_iff a z2 x)
  · ext x
    change S.coveredTwoBoundaryCode r a z1 (S.coveredLabel a x) = 4 ↔ x ∈ S.D
    rw [(hc (S.coveredLabel a x)).2.2.2.2]
    simp [S.coveredLabel_eq_inr_iff]

theorem coveredTwoBoundaryLabel_fibers_positive (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2)
    (hD : 0 < μ S.D) (i : Fin 5) : 0 < μ (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {i}) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    S.coveredTwoBoundaryLabel_fibers r a z1 z2 hra hz1r hz1a hz2r hz2a hz12 hatoms
  fin_cases i
  · change 0 < μ (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {0})
    rw [h0]; exact (S.hfibers a.val a.property).2.1
  · change 0 < μ (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {1})
    rw [h1]; exact (S.hfibers r.val r.property).2.1
  · change 0 < μ (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {2})
    rw [h2]; exact (S.hfibers z1.val z1.property).2.1
  · change 0 < μ (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {3})
    rw [h3]; exact (S.hfibers z2.val z2.property).2.1
  · change 0 < μ (S.coveredTwoBoundaryLabel r a z1 ⁻¹' {4})
    rwa [h4]

/-- The inverse is exact away from the old R label; R will be null in
its physical application, rather than discarded pointwise. -/
theorem coveredTwoBoundaryIndex_code (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2)
    (i : S.I ⊕ Bool) (hi : i ≠ Sum.inr true) :
    S.coveredTwoBoundaryIndex r a z1 z2 (S.coveredTwoBoundaryCode r a z1 i) = i := by
  cases i with
  | inl u =>
    rcases hatoms u with rfl | rfl | rfl | rfl <;>
      simp [coveredTwoBoundaryCode, coveredTwoBoundaryIndex, hra, hz1r, hz1a, hz2r, hz2a,
        Ne.symm hz12]
  | inr b => cases b <;> simp_all [coveredTwoBoundaryCode, coveredTwoBoundaryIndex]

theorem coveredGraph_twoBoundaryIndex (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    (hra : r ≠ a) (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2) (i j : Fin 5) :
    S.coveredGraph r a (S.coveredTwoBoundaryIndex r a z1 z2 i)
      (S.coveredTwoBoundaryIndex r a z1 z2 j) =
      CoveredTwoExterior.blockAdjacency i j := by
  fin_cases i <;> fin_cases j <;>
    simp [coveredGraph, coveredTwoBoundaryIndex, CoveredTwoExterior.blockAdjacency,
      hra, hz1r, hz1a, hz2r, hz2a, hz12,
      Ne.symm hra, Ne.symm hz1r, Ne.symm hz1a, Ne.symm hz2r, Ne.symm hz2a, Ne.symm hz12]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Collapsing a null R region gives the actual original boundary graph
almost everywhere. Neither R positivity nor a new graph is assumed. -/
theorem ae_covered_two_boundary_graph (S : SelectedHighLowStructure W m) (r a z1 z2 : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hz1r : z1 ≠ r) (hz1a : z1 ≠ a) (hz2r : z2 ≠ r) (hz2a : z2 ≠ a)
    (hz12 : z1 ≠ z2)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z1 ∨ u = z2) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if CoveredTwoExterior.blockAdjacency
        (S.coveredTwoBoundaryLabel r a z1 p.1) (S.coveredTwoBoundaryLabel r a z1 p.2) = true
        then 1 else 0 := by
  have hn : ∀ᵐ x ∂μ, S.coveredLabel a x ≠ Sum.inr true := by
    apply measure_eq_zero_iff_ae_notMem.mp
    change μ (S.coveredLabel a ⁻¹' {Sum.inr true}) = 0
    rw [S.coveredLabel_fiber_true]
    exact hR
  filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
    Measure.quasiMeasurePreserving_fst.ae hn,
    Measure.quasiMeasurePreserving_snd.ae hn] with p hp h1 h2
  have he (x : Ω) (hx : S.coveredLabel a x ≠ Sum.inr true) : S.coveredLabel a x =
      S.coveredTwoBoundaryIndex r a z1 z2 (S.coveredTwoBoundaryLabel r a z1 x) :=
    (S.coveredTwoBoundaryIndex_code r a z1 z2 hpair.1 hz1r hz1a hz2r hz2a hz12 hatoms _ hx).symm
  rw [he p.1 h1, he p.2 h2, S.coveredGraph_twoBoundaryIndex r a z1 z2 hpair.1
    hz1r hz1a hz2r hz2a hz12] at hp
  exact hp

end Erdos1017.CappedModel.SelectedHighLowStructure
