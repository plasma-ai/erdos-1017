module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.Covered.CoveredOneExteriorBlocks

/-!
# Boundary labeling for the one-exterior case

This module defines the four-label boundary coding `coveredBoundaryLabel`, which
merges both diffuse regions into the `D` fiber and orders the labels
`A, B, C, E`, and its partial inverse `coveredBoundaryIndex`, exact away from
the `R` region. If the `R` region is null, the coded graph agrees almost
everywhere with the original boundary graph (`ae_covered_boundary_graph`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Collapse both diffuse regions to the literal original D fiber.
The finite order is A, B, C, E. -/
def coveredBoundaryCode (S : SelectedHighLowStructure W m) (r a : S.I) : S.I ⊕ Bool → Fin 4
  | Sum.inl u => if u = a then 0 else if u = r then 1 else 2
  | Sum.inr _ => 3

def coveredBoundaryLabel (S : SelectedHighLowStructure W m) (r a : S.I) (x : Ω) : Fin 4 :=
  S.coveredBoundaryCode r a (S.coveredLabel a x)

def coveredBoundaryIndex (S : SelectedHighLowStructure W m) (r a z : S.I) :
    Fin 4 → S.I ⊕ Bool := ![Sum.inl a, Sum.inl r, Sum.inl z, Sum.inr false]

theorem measurable_coveredBoundaryLabel (S : SelectedHighLowStructure W m) (r a : S.I) :
    Measurable (S.coveredBoundaryLabel r a) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable (S.coveredBoundaryCode r a)).comp (S.measurable_coveredLabel a)

/-- The diffuse fiber is D exactly, even before the R-null assumption. -/
theorem coveredBoundaryLabel_fibers (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    (S.coveredBoundaryLabel r a ⁻¹' {0}) = {x | S.ρ x = a.val} ∧
    (S.coveredBoundaryLabel r a ⁻¹' {1}) = {x | S.ρ x = r.val} ∧
    (S.coveredBoundaryLabel r a ⁻¹' {2}) = {x | S.ρ x = z.val} ∧
    (S.coveredBoundaryLabel r a ⁻¹' {3}) = S.D := by
  have hc (i : S.I ⊕ Bool) :
      (S.coveredBoundaryCode r a i = 0 ↔ i = Sum.inl a) ∧
      (S.coveredBoundaryCode r a i = 1 ↔ i = Sum.inl r) ∧
      (S.coveredBoundaryCode r a i = 2 ↔ i = Sum.inl z) ∧
      (S.coveredBoundaryCode r a i = 3 ↔ ∃ b, i = Sum.inr b) := by
    cases i with
    | inl u =>
      rcases hatoms u with rfl | rfl | rfl <;>
        simp [coveredBoundaryCode, hra, hzr, hza, Ne.symm hra, Ne.symm hzr, Ne.symm hza]
    | inr b => simp [coveredBoundaryCode]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    exact (hc (S.coveredLabel a x)).1.trans (S.coveredLabel_eq_inl_iff a a x)
  · ext x
    exact (hc (S.coveredLabel a x)).2.1.trans (S.coveredLabel_eq_inl_iff a r x)
  · ext x
    exact (hc (S.coveredLabel a x)).2.2.1.trans (S.coveredLabel_eq_inl_iff a z x)
  · ext x
    change S.coveredBoundaryCode r a (S.coveredLabel a x) = 3 ↔ x ∈ S.D
    rw [(hc (S.coveredLabel a x)).2.2.2]
    simp [S.coveredLabel_eq_inr_iff]

theorem coveredBoundaryLabel_fibers_positive (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z)
    (hD : 0 < μ S.D) (i : Fin 4) : 0 < μ (S.coveredBoundaryLabel r a ⁻¹' {i}) := by
  obtain ⟨h0, h1, h2, h3⟩ := S.coveredBoundaryLabel_fibers r a z hra hzr hza hatoms
  fin_cases i
  · change 0 < μ (S.coveredBoundaryLabel r a ⁻¹' {0})
    rw [h0]; exact (S.hfibers a.val a.property).2.1
  · change 0 < μ (S.coveredBoundaryLabel r a ⁻¹' {1})
    rw [h1]; exact (S.hfibers r.val r.property).2.1
  · change 0 < μ (S.coveredBoundaryLabel r a ⁻¹' {2})
    rw [h2]; exact (S.hfibers z.val z.property).2.1
  · change 0 < μ (S.coveredBoundaryLabel r a ⁻¹' {3})
    rwa [h3]

/-- The inverse is exact away from the old R label; R will be null in
its physical application, rather than discarded pointwise. -/
theorem coveredBoundaryIndex_code (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z)
    (i : S.I ⊕ Bool) (hi : i ≠ Sum.inr true) :
    S.coveredBoundaryIndex r a z (S.coveredBoundaryCode r a i) = i := by
  cases i with
  | inl u =>
    rcases hatoms u with rfl | rfl | rfl <;>
      simp [coveredBoundaryCode, coveredBoundaryIndex, hra, hzr, hza]
  | inr b => cases b <;> simp_all [coveredBoundaryCode, coveredBoundaryIndex]

theorem coveredGraph_boundaryIndex (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a) (i j : Fin 4) :
    S.coveredGraph r a (S.coveredBoundaryIndex r a z i) (S.coveredBoundaryIndex r a z j) =
      CoveredOneExterior.blockAdjacency i j := by
  fin_cases i <;> fin_cases j <;>
    simp [coveredGraph, coveredBoundaryIndex, CoveredOneExterior.blockAdjacency,
      hra, hzr, hza, Ne.symm hra, Ne.symm hzr, Ne.symm hza]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Collapsing a null R region gives the actual original boundary graph
almost everywhere. Neither R positivity nor a new graph is assumed. -/
theorem ae_covered_boundary_graph (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if CoveredOneExterior.blockAdjacency
        (S.coveredBoundaryLabel r a p.1) (S.coveredBoundaryLabel r a p.2) = true then 1 else 0 := by
  have hn : ∀ᵐ x ∂μ, S.coveredLabel a x ≠ Sum.inr true := by
    apply measure_eq_zero_iff_ae_notMem.mp
    change μ (S.coveredLabel a ⁻¹' {Sum.inr true}) = 0
    rw [S.coveredLabel_fiber_true]
    exact hR
  filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
    Measure.quasiMeasurePreserving_fst.ae hn,
    Measure.quasiMeasurePreserving_snd.ae hn] with p hp h1 h2
  have he (x : Ω) (hx : S.coveredLabel a x ≠ Sum.inr true) : S.coveredLabel a x =
      S.coveredBoundaryIndex r a z (S.coveredBoundaryLabel r a x) :=
    (S.coveredBoundaryIndex_code r a z hpair.1 hzr hza hatoms _ hx).symm
  rw [he p.1 h1, he p.2 h2, S.coveredGraph_boundaryIndex r a z hpair.1 hzr hza] at hp
  exact hp

end Erdos1017.CappedModel.SelectedHighLowStructure
