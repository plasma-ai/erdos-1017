module

public import Erdos1017.SelectedModel.ZeroClass.CountableZeroClassReplacement

/-!
# Benchmark inequality at index one

Full feasibility together with a stationary nonnegative shifted operator of
positive index at most one implies the benchmark inequality
(`full_objective_le_benchmark_of_index_one`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

universe u

/-- Actual full feasibility and a stationary nonnegative shifted operator
of positive index at most one imply the benchmark inequality. The countable
feature, active classes and multipartite replacement are all constructed. -/
theorem full_objective_le_benchmark_of_index_one
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) (hW : FullFeasible W) (m ν : ℝ)
    (hm : m ∈ Set.Icc (-3 : ℝ) 1) (hν : 0 < ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν)
    (hnonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ shiftedMoment W m p)
    (hcomp : ∀ᵐ p ∂μ.prod μ,
      (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (hfinite : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)))
    (hindex : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 1) :
    objective W ≤ benchmark (density W) := by
  obtain ⟨ι, hcount, F, C, hF, _, hrep, hzero, hdata⟩ :=
    exists_index_one_active_classes W m ν hν hnonneg hrow hcomp hfinite hindex
  have : Countable ι := hcount
  let b : HilbertBasis ι ℝ (lp (fun _ : ι => ℝ) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have hsep := ((Set.countable_range b).isSeparable.span (R := ℝ)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] at hsep
  have : TopologicalSpace.SeparableSpace (lp (fun _ : ι => ℝ) 2) :=
    TopologicalSpace.isSeparable_univ_iff.mp hsep
  let : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
  have : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
  exact objective_le_benchmark_of_active_boundary_data W hW F hF.measurable C ν m hν.le hm
    hdata hrep hzero hnonneg hcomp hdet

end Erdos1017.CappedModel
