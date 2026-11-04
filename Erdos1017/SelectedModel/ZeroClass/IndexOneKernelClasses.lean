module

public import Erdos1017.SelectedModel.ZeroClass.IndexOneKernelGeometry
public import Erdos1017.SelectedModel.ZeroClass.IndexOneZeroClasses

/-!
# Feature and zero classes of an index-one operator

The index-one operator hypotheses construct both the Hilbert feature and its
countably many positive-measure boundary zero classes
(`exists_index_one_feature_zero_classes`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

universe u

/-- The actual index-one operator hypotheses construct both the Hilbert
feature and its countably many positive-measure boundary zero classes. -/
theorem exists_index_one_feature_zero_classes
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (K : Ω → Ω → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hK : AEStronglyMeasurable (fun z : Ω × Ω => K z.1 z.2) (μ.prod μ))
    (hB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖K z.1 z.2‖ ≤ B)
    (hK0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, 0 ≤ K z.1 z.2)
    (hsym : ∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = K z.2 z.1)
    (ν : ℝ) (hν : 0 < ν) (hstationary : ∀ᵐ x ∂μ, (∫ y, K x y ∂μ) = ν)
    (hfinite : FiniteDimensional ℝ (positiveSpectralSubspace (operator K hB0 hK hB)))
    (hindex : Module.finrank ℝ (positiveSpectralSubspace (operator K hB0 hK hB)) ≤ 1) :
    ∃ (ι : Type u) (_ : Countable ι) (V : Ω → lp (fun _ : ι => ℝ) 2)
      (A : Set (lp (fun _ : ι => ℝ) 2)),
      StronglyMeasurable V ∧
      (∀ᵐ x ∂μ, ‖V x‖ ≤ Real.sqrt ν) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = ν - ⟪V z.1, V z.2⟫) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ,
        K z.1 z.2 = 0 ↔ ‖V z.1‖ = Real.sqrt ν ∧ V z.1 = V z.2) ∧
      A.Countable ∧
      (∀ v ∈ A, MeasurableSet {x | V x = v} ∧
        0 < μ {x | V x = v} ∧ ‖v‖ = Real.sqrt ν) ∧
      A.Pairwise (fun v w => Disjoint {x | V x = v} {x | V x = w}) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, K z.1 z.2 = 0 ↔
        ∃ v ∈ A, V z.1 = v ∧ V z.2 = v) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ,
        (¬∃ v ∈ A, V z.1 = v ∧ V z.2 = v) → 0 < K z.1 z.2) := by
  obtain ⟨ι, hcount, V, hVm, hbound, hrep, hzero⟩ :=
    exists_index_one_feature K hB0 hK hB hK0 hsym ν hν hstationary hfinite hindex
  let := hcount
  let e : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range e).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe] at hsep
  let := TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  let : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  obtain ⟨A, hA, hclass, hdisjoint, hclasses⟩ :=
    exists_countable_boundary_zero_classes V hVm.measurable K (Real.sqrt ν) hzero
  refine ⟨ι, hcount, V, A, hVm, hbound, hrep, hzero, hA, ?_, hdisjoint, hclasses, ?_⟩
  · intro v hv
    exact ⟨(hclass v hv).1, (hclass v hv).2.1, (hclass v hv).2.2.2⟩
  · filter_upwards [hK0, hclasses] with z hz hclasses
    intro hout
    exact lt_of_le_of_ne hz (Ne.symm (fun h => hout (hclasses.mp h)))

end Erdos1017.KernelOperator
