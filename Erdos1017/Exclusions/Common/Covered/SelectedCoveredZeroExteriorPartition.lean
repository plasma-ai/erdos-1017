module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.Covered.CoveredZeroExteriorBlocks

/-!
# Finite partition with no exterior atom

The code `coveredZeroBoundaryCode` merges both diffuse regions into the `D`
fiber and orders the labels `A`, `B`, `E`, with a measurable label and a partial
inverse exact away from the `R` region; if the `R` region is null, the coded
graph agrees almost everywhere with the original boundary graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Collapse both diffuse regions to the literal original D fiber.
The finite order is A, B, E. -/
def coveredZeroBoundaryCode (S : SelectedHighLowStructure W m) (r a : S.I) : S.I ⊕ Bool → Fin 3
  | Sum.inl u => if u = a then 0 else if u = r then 1 else 2
  | Sum.inr _ => 2

def coveredZeroBoundaryLabel (S : SelectedHighLowStructure W m) (r a : S.I) (x : Ω) : Fin 3 :=
  S.coveredZeroBoundaryCode r a (S.coveredLabel a x)

def coveredZeroBoundaryIndex (S : SelectedHighLowStructure W m) (r a : S.I) :
    Fin 3 → S.I ⊕ Bool := ![Sum.inl a, Sum.inl r, Sum.inr false]

theorem measurable_coveredZeroBoundaryLabel (S : SelectedHighLowStructure W m) (r a : S.I) :
    Measurable (S.coveredZeroBoundaryLabel r a) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable (S.coveredZeroBoundaryCode r a)).comp (S.measurable_coveredLabel a)

/-- The diffuse fiber is D exactly, even before the R-null assumption. -/
theorem coveredZeroBoundaryLabel_fibers (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    (S.coveredZeroBoundaryLabel r a ⁻¹' {0}) = {x | S.ρ x = a.val} ∧
    (S.coveredZeroBoundaryLabel r a ⁻¹' {1}) = {x | S.ρ x = r.val} ∧
    (S.coveredZeroBoundaryLabel r a ⁻¹' {2}) = S.D := by
  have hc (i : S.I ⊕ Bool) :
      (S.coveredZeroBoundaryCode r a i = 0 ↔ i = Sum.inl a) ∧
      (S.coveredZeroBoundaryCode r a i = 1 ↔ i = Sum.inl r) ∧
      (S.coveredZeroBoundaryCode r a i = 2 ↔ ∃ b, i = Sum.inr b) := by
    cases i with
    | inl u =>
      rcases hatoms u with rfl | rfl <;>
        simp [coveredZeroBoundaryCode, hra, Ne.symm hra]
    | inr b => simp [coveredZeroBoundaryCode]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact (hc (S.coveredLabel a x)).1.trans (S.coveredLabel_eq_inl_iff a a x)
  · ext x
    exact (hc (S.coveredLabel a x)).2.1.trans (S.coveredLabel_eq_inl_iff a r x)
  · ext x
    change S.coveredZeroBoundaryCode r a (S.coveredLabel a x) = 2 ↔ x ∈ S.D
    rw [(hc (S.coveredLabel a x)).2.2]
    simp [S.coveredLabel_eq_inr_iff]

theorem coveredZeroBoundaryLabel_fibers_positive (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a)
    (hD : 0 < μ S.D) (i : Fin 3) : 0 < μ (S.coveredZeroBoundaryLabel r a ⁻¹' {i}) := by
  obtain ⟨h0, h1, h2⟩ := S.coveredZeroBoundaryLabel_fibers r a hra hatoms
  fin_cases i
  · change 0 < μ (S.coveredZeroBoundaryLabel r a ⁻¹' {0})
    rw [h0]; exact (S.hfibers a.val a.property).2.1
  · change 0 < μ (S.coveredZeroBoundaryLabel r a ⁻¹' {1})
    rw [h1]; exact (S.hfibers r.val r.property).2.1
  · change 0 < μ (S.coveredZeroBoundaryLabel r a ⁻¹' {2})
    rwa [h2]

/-- The inverse is exact away from the old R label; R will be null in
its physical application, rather than discarded pointwise. -/
theorem coveredZeroBoundaryIndex_code (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a)
    (i : S.I ⊕ Bool) (hi : i ≠ Sum.inr true) :
    S.coveredZeroBoundaryIndex r a (S.coveredZeroBoundaryCode r a i) = i := by
  cases i with
  | inl u =>
    rcases hatoms u with rfl | rfl <;>
      simp [coveredZeroBoundaryCode, coveredZeroBoundaryIndex, hra]
  | inr b => cases b <;> simp_all [coveredZeroBoundaryCode, coveredZeroBoundaryIndex]

theorem coveredGraph_zeroBoundaryIndex (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a) (i j : Fin 3) :
    S.coveredGraph r a (S.coveredZeroBoundaryIndex r a i) (S.coveredZeroBoundaryIndex r a j) =
      CoveredZeroExterior.blockAdjacency i j := by
  fin_cases i <;> fin_cases j <;>
    simp [coveredGraph, coveredZeroBoundaryIndex, CoveredZeroExterior.blockAdjacency,
      hra, Ne.symm hra]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Collapsing a null R region gives the actual original boundary graph
almost everywhere. Neither R positivity nor a new graph is assumed. -/
theorem ae_covered_zero_boundary_graph (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : μ (S.D ∩ S.rootNeighborhood a) = 0)
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if CoveredZeroExterior.blockAdjacency
        (S.coveredZeroBoundaryLabel r a p.1) (S.coveredZeroBoundaryLabel r a p.2) = true
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
      S.coveredZeroBoundaryIndex r a (S.coveredZeroBoundaryLabel r a x) :=
    (S.coveredZeroBoundaryIndex_code r a hpair.1 hatoms _ hx).symm
  rw [he p.1 h1, he p.2 h2, S.coveredGraph_zeroBoundaryIndex r a hpair.1] at hp
  exact hp

end Erdos1017.CappedModel.SelectedHighLowStructure
