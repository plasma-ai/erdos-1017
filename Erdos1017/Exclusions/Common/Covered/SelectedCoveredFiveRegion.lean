module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.Covered.CoveredCBlockPerturbation

/-!
# The five-region labeling with one exterior atom

This module defines the five-region code and label on `A, B, C, R, E`,
invertible when `C` is the only exterior atom, shows the five fibers are the
original regions under the original law, and that the covered topology realizes
the five-region perturbation graph almost everywhere under the one-exterior-atom
hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- The five-region order is A, B, C, R, E. Invertibility requires the
explicit statement that C is the only exterior atom. -/
def coveredFiveCode (S : SelectedHighLowStructure W m) (r a : S.I) : S.I ⊕ Bool → Fin 5
  | Sum.inl u => if u = a then 0 else if u = r then 1 else 2
  | Sum.inr true => 3
  | Sum.inr false => 4

def coveredFiveLabel (S : SelectedHighLowStructure W m) (r a : S.I) (x : Ω) : Fin 5 :=
  S.coveredFiveCode r a (S.coveredLabel a x)

def coveredFiveIndex (S : SelectedHighLowStructure W m) (r a z : S.I) :
    Fin 5 → S.I ⊕ Bool :=
  ![Sum.inl a, Sum.inl r, Sum.inl z, Sum.inr true, Sum.inr false]

theorem coveredFiveCode_index (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a) (i : Fin 5) :
    S.coveredFiveCode r a (S.coveredFiveIndex r a z i) = i := by
  fin_cases i <;> simp [coveredFiveCode, coveredFiveIndex, hra, hzr, hza]

theorem coveredFiveIndex_code (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) (i : S.I ⊕ Bool) :
    S.coveredFiveIndex r a z (S.coveredFiveCode r a i) = i := by
  cases i with
  | inl u =>
    rcases hatoms u with hur | hua | huz
    · subst u
      by_cases hra : r = a
      · simp [coveredFiveCode, coveredFiveIndex, hra]
      · simp [coveredFiveCode, coveredFiveIndex, hra]
    · subst u
      simp [coveredFiveCode, coveredFiveIndex]
    · subst u
      by_cases hza : z = a
      · simp [coveredFiveCode, coveredFiveIndex, hza]
      · by_cases hzr : z = r
        · subst z
          simp [coveredFiveCode, coveredFiveIndex, hza]
        · simp [coveredFiveCode, coveredFiveIndex, hza, hzr]
  | inr b => cases b <;> rfl

theorem measurable_coveredFiveLabel (S : SelectedHighLowStructure W m) (r a : S.I) :
    Measurable (S.coveredFiveLabel r a) := by
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  exact (measurable_of_countable (S.coveredFiveCode r a)).comp (S.measurable_coveredLabel a)

/-- All five fibers are literal original regions under the original law. -/
theorem coveredFiveLabel_fibers (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    (S.coveredFiveLabel r a ⁻¹' {0}) = {x | S.ρ x = a.val} ∧
    (S.coveredFiveLabel r a ⁻¹' {1}) = {x | S.ρ x = r.val} ∧
    (S.coveredFiveLabel r a ⁻¹' {2}) = {x | S.ρ x = z.val} ∧
    (S.coveredFiveLabel r a ⁻¹' {3}) = S.D ∩ S.rootNeighborhood a ∧
    (S.coveredFiveLabel r a ⁻¹' {4}) = S.D \ S.rootNeighborhood a := by
  have he (i : Fin 5) : S.coveredFiveLabel r a ⁻¹' {i} =
      S.coveredLabel a ⁻¹' {S.coveredFiveIndex r a z i} := by
    ext x
    change S.coveredFiveCode r a (S.coveredLabel a x) = i ↔
      S.coveredLabel a x = S.coveredFiveIndex r a z i
    constructor
    · intro h
      rw [← S.coveredFiveIndex_code r a z hatoms (S.coveredLabel a x), h]
    · intro h
      rw [h, S.coveredFiveCode_index r a z hra hzr hza]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he 0]; exact S.coveredLabel_fiber_inl a a
  · rw [he 1]; exact S.coveredLabel_fiber_inl a r
  · rw [he 2]; exact S.coveredLabel_fiber_inl a z
  · rw [he 3]; exact S.coveredLabel_fiber_true a
  · rw [he 4]; exact S.coveredLabel_fiber_false a

theorem coveredFiveLabel_fibers_positive (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i : Fin 5) :
    0 < μ (S.coveredFiveLabel r a ⁻¹' {i}) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := S.coveredFiveLabel_fibers r a z hra hzr hza hatoms
  fin_cases i
  · change 0 < μ (S.coveredFiveLabel r a ⁻¹' {0})
    rw [h0]; exact (S.hfibers a.val a.property).2.1
  · change 0 < μ (S.coveredFiveLabel r a ⁻¹' {1})
    rw [h1]; exact (S.hfibers r.val r.property).2.1
  · change 0 < μ (S.coveredFiveLabel r a ⁻¹' {2})
    rw [h2]; exact (S.hfibers z.val z.property).2.1
  · change 0 < μ (S.coveredFiveLabel r a ⁻¹' {3})
    rwa [h3]
  · change 0 < μ (S.coveredFiveLabel r a ⁻¹' {4})
    rwa [h4]

/-- The original covered graph restricted to the five literal labels
is the finite perturbation graph, with C still present. -/
theorem coveredGraph_fiveIndex (S : SelectedHighLowStructure W m) (r a z : S.I)
    (hra : r ≠ a) (hzr : z ≠ r) (hza : z ≠ a) (i j : Fin 5) :
    S.coveredGraph r a (S.coveredFiveIndex r a z i) (S.coveredFiveIndex r a z j) =
      CoveredC.blockAdjacency i j := by
  fin_cases i <;> fin_cases j <;>
    simp [coveredGraph, coveredFiveIndex, CoveredC.blockAdjacency,
      hra, hzr, hza, Ne.symm hra, Ne.symm hzr, Ne.symm hza]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Original covered topology realizes the actual five-region graph
under the one-exterior-atom hypothesis. -/
theorem ae_covered_five_graph (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hzr : z ≠ r) (hza : z ≠ a)
    (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    ∀ᵐ p ∂μ.prod μ, PhysicalRepresentative.adjacency W m p.1 p.2 =
      CoveredC.blockAdjacency (S.coveredFiveLabel r a p.1) (S.coveredFiveLabel r a p.2) := by
  filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
    PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with p hg hp
  have he (x : Ω) : S.coveredLabel a x =
      S.coveredFiveIndex r a z (S.coveredFiveLabel r a x) :=
    (S.coveredFiveIndex_code r a z hatoms (S.coveredLabel a x)).symm
  rw [he p.1, he p.2, S.coveredGraph_fiveIndex r a z hpair.1 hzr hza] at hg
  change W.moment CappedColor.adjacency p = _ at hg
  have hh := hp.symm.trans hg
  cases h0 : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    cases h1 : CoveredC.blockAdjacency (S.coveredFiveLabel r a p.1)
      (S.coveredFiveLabel r a p.2) <;> simp_all

end Erdos1017.CappedModel.SelectedHighLowStructure
