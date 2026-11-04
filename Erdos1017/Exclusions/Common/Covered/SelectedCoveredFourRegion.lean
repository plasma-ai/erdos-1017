module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockGeometry

/-!
# The four-region labeling without exterior atoms

This module collapses the covered label alphabet to `A, B, R, E`, with an exact
inverse once exterior atoms are absent, shows the four fibers are the original
atom and diffuse regions, and that the covered topology then gives the
four-region physical graph almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Collapse the covered label alphabet to A, B, R, E. Its exact inverse
is proved only under the explicit absence of exterior atoms. -/
def coveredFourCode (S : SelectedHighLowStructure W m) (a : S.I) : S.I ⊕ Bool → Fin 4
  | Sum.inl u => if u = a then 0 else 1
  | Sum.inr true => 2
  | Sum.inr false => 3

def coveredFourLabel (S : SelectedHighLowStructure W m) (a : S.I) (x : Ω) : Fin 4 :=
  S.coveredFourCode a (S.coveredLabel a x)

def coveredFourIndex (S : SelectedHighLowStructure W m) (r a : S.I) : Fin 4 → S.I ⊕ Bool :=
  ![Sum.inl a, Sum.inl r, Sum.inr true, Sum.inr false]

theorem coveredFourCode_index (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a) (i : Fin 4) :
    S.coveredFourCode a (S.coveredFourIndex r a i) = i := by
  fin_cases i <;> simp [coveredFourCode, coveredFourIndex, hra]

theorem coveredFourIndex_code (S : SelectedHighLowStructure W m) (r a : S.I)
    (hatoms : ∀ u : S.I, u = r ∨ u = a) (i : S.I ⊕ Bool) :
    S.coveredFourIndex r a (S.coveredFourCode a i) = i := by
  cases i with
  | inl u =>
    by_cases hua : u = a
    · simp [coveredFourCode, coveredFourIndex, hua]
    · have hur := (hatoms u).resolve_right hua
      rw [coveredFourCode, ite_eq_right hua]
      simpa only [coveredFourIndex, Matrix.cons_val_one, Matrix.cons_val_zero] using
        congrArg Sum.inl hur.symm
  | inr b => cases b <;> rfl

theorem measurable_coveredFourLabel (S : SelectedHighLowStructure W m) (a : S.I) :
    Measurable (S.coveredFourLabel a) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable (S.coveredFourCode a)).comp (S.measurable_coveredLabel a)

/-- The four fibers are the literal original atom and diffuse regions,
not replacements modulo a newly chosen law. -/
theorem coveredFourLabel_fibers (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a) (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    (S.coveredFourLabel a ⁻¹' {0}) = {x | S.ρ x = a.val} ∧
    (S.coveredFourLabel a ⁻¹' {1}) = {x | S.ρ x = r.val} ∧
    (S.coveredFourLabel a ⁻¹' {2}) = S.D ∩ S.rootNeighborhood a ∧
    (S.coveredFourLabel a ⁻¹' {3}) = S.D \ S.rootNeighborhood a := by
  have he (i : Fin 4) : S.coveredFourLabel a ⁻¹' {i} =
      S.coveredLabel a ⁻¹' {S.coveredFourIndex r a i} := by
    ext x
    change S.coveredFourCode a (S.coveredLabel a x) = i ↔
      S.coveredLabel a x = S.coveredFourIndex r a i
    constructor
    · intro h
      rw [← S.coveredFourIndex_code r a hatoms (S.coveredLabel a x), h]
    · intro h
      rw [h, S.coveredFourCode_index r a hra]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he 0]; exact S.coveredLabel_fiber_inl a a
  · rw [he 1]; exact S.coveredLabel_fiber_inl a r
  · rw [he 2]; exact S.coveredLabel_fiber_true a
  · rw [he 3]; exact S.coveredLabel_fiber_false a

theorem coveredFourLabel_fibers_positive (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a) (hatoms : ∀ u : S.I, u = r ∨ u = a)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i : Fin 4) :
    0 < μ (S.coveredFourLabel a ⁻¹' {i}) := by
  obtain ⟨h0, h1, h2, h3⟩ := S.coveredFourLabel_fibers r a hra hatoms
  fin_cases i
  · change 0 < μ (S.coveredFourLabel a ⁻¹' {0})
    rw [h0]; exact (S.hfibers a.val a.property).2.1
  · change 0 < μ (S.coveredFourLabel a ⁻¹' {1})
    rw [h1]; exact (S.hfibers r.val r.property).2.1
  · change 0 < μ (S.coveredFourLabel a ⁻¹' {2})
    rwa [h2]
  · change 0 < μ (S.coveredFourLabel a ⁻¹' {3})
    rwa [h3]

/-- The old covered graph is exactly the four-region table on its four
literal original labels. -/
theorem coveredGraph_fourIndex (S : SelectedHighLowStructure W m) (r a : S.I)
    (hra : r ≠ a) (i j : Fin 4) :
    S.coveredGraph r a (S.coveredFourIndex r a i) (S.coveredFourIndex r a j) =
      TwoAtomCountGate.blockAdjacency i j := by
  fin_cases i <;> fin_cases j <;>
    simp [coveredGraph, coveredFourIndex, TwoAtomCountGate.blockAdjacency, hra, Ne.symm hra]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Original covered topology gives the actual four-region physical
graph once the absence of exterior atoms has been established. -/
theorem ae_covered_four_graph (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hatoms : ∀ u : S.I, u = r ∨ u = a) :
    ∀ᵐ p ∂μ.prod μ, PhysicalRepresentative.adjacency W m p.1 p.2 =
      TwoAtomCountGate.blockAdjacency (S.coveredFourLabel a p.1) (S.coveredFourLabel a p.2) := by
  filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hg hp
  have he (x : Ω) : S.coveredLabel a x =
      S.coveredFourIndex r a (S.coveredFourLabel a x) :=
    (S.coveredFourIndex_code r a hatoms (S.coveredLabel a x)).symm
  rw [he p.1, he p.2, S.coveredGraph_fourIndex r a hpair.1] at hg
  change W.moment CappedColor.adjacency p = _ at hg
  have hh := hp.symm.trans hg
  cases h0 : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    cases h1 : TwoAtomCountGate.blockAdjacency (S.coveredFourLabel a p.1)
      (S.coveredFourLabel a p.2) <;> simp_all

end Erdos1017.CappedModel.SelectedHighLowStructure
