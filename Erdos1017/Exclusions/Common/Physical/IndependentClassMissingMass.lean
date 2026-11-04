module

public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence
public import Erdos1017.SelectedModel.Flows.FullForwardPeakAtom

/-!
# Independent class squares inside the missing density

The squares of the independent class masses, and in particular of any two
distinct independent atoms, sum to at most the missing density of the original
model, with no condition on pairs outside those squares.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

namespace Erdos1017.MultipartiteClassMasses

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

local instance : MeasurableSpace (Option ι) := ⊤

/-- Independent class squares contribute to the original missing density,
without any condition on pairs outside those squares. -/
theorem tsum_classMass_sq_le_missing_density (W : CappedModel.Model Ω μ)
    (q : Ω → Option ι) (hq : Measurable q)
    (hzero : ∀ᵐ p ∂μ.prod μ, p ∈ independentPairs q →
      W.moment CappedColor.adjacency p = 0) :
    (∑' i, (classMass μ q i) ^ 2) ≤ 1 - 2 * CappedModel.density W := by
  have hmeas := independentPairs_measurable q hq
  have ha := CappedModel.integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  have hle : (∫ p, (independentPairs q).indicator (fun _ => (1 : ℝ)) p ∂μ.prod μ) ≤
      ∫ p, 1 - W.moment CappedColor.adjacency p ∂μ.prod μ := by
    apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator hmeas)
      ((integrable_const 1).sub ha)
    filter_upwards [hzero] with p hp
    change (independentPairs q).indicator (fun _ => (1 : ℝ)) p ≤
      1 - W.moment CappedColor.adjacency p
    by_cases h : p ∈ independentPairs q
    · simp only [indicator_of_mem h, hp h, sub_zero, le_refl]
    · simp only [indicator_of_notMem h]
      exact sub_nonneg.mpr (CappedModel.adjacency_moment_mem W p).2
  rw [integral_indicator hmeas, setIntegral_const, smul_eq_mul, mul_one,
    independentPairs_mass q hq, integral_sub (integrable_const 1) ha] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  unfold CappedModel.density
  linarith

end Erdos1017.MultipartiteClassMasses

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- The actual original independent squares give a lower bound, rather
than a multipartite equality, for this original model's missing density. -/
theorem originalAtomMass_sq_sum_le_missing_density (S : SelectedHighLowStructure W m) :
    (∑' i, (S.originalAtomMass i) ^ 2) ≤ 1 - 2 * density W := by
  let : Countable S.I := S.hI.to_subtype
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hz := HalfGraphMultipartite.ae_sameAtom_adjacency_zero
    (adjacencyKernel W) S.ρ S.hρ.measurable S.I S.hI
    (fun r hr => (S.hfibers r hr).2.2.1)
  have hzero : ∀ᵐ p ∂μ.prod μ,
      p ∈ MultipartiteClassMasses.independentPairs S.collapsedPartLabel →
        W.moment CappedColor.adjacency p = 0 := by
    filter_upwards [hz] with p hp hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    rw [S.collapsedPartLabel_fiber i] at hi
    exact hp ⟨i.val, i.property, hi.1, hi.2⟩
  have h := MultipartiteClassMasses.tsum_classMass_sq_le_missing_density
    W S.collapsedPartLabel S.measurable_collapsedPartLabel hzero
  convert h using 1
  apply tsum_congr
  intro i
  rw [MultipartiteClassMasses.classMass, S.collapsedPartLabel_fiber i]
  rfl

/-- Two distinct original independent atoms contribute their two disjoint
squares, regardless of the original graph between or outside the atoms. -/
theorem two_originalAtomMass_sq_le_missing_density (S : SelectedHighLowStructure W m)
    (i j : S.I) (hne : i ≠ j) :
    (S.originalAtomMass i) ^ 2 + (S.originalAtomMass j) ^ 2 ≤ 1 - 2 * density W := by
  let : Countable S.I := S.hI.to_subtype
  have hs : Summable (fun i => (S.originalAtomMass i) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ S.originalAtomMass_summable.2
    intro i
    have hn := S.originalAtomMass_summable.1 i
    have hb : S.originalAtomMass i ≤ 1 := measureReal_le_one
    nlinarith
  have h := Summable.sum_le_tsum (s := {i, j}) (fun k _ => sq_nonneg (S.originalAtomMass k)) hs
  simpa only [Finset.sum_pair hne] using h.trans S.originalAtomMass_sq_sum_le_missing_density

end Erdos1017.CappedModel.SelectedHighLowStructure
