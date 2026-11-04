module

public import Erdos1017.Models.Capped.CappedKernelOperator
public import Erdos1017.Models.Kernel.KernelReindexing
public import Erdos1017.Models.Kernel.WeightRegularity

/-!
# Regularity under operator-norm convergence

Operator-norm convergence of the adjacency operators preserves nonzero first
variation and regularity eventually, and regularity passes back from a
measure-preserving reindexing to the original model, so one common sequence of
alignments transfers eventual regularity to the original models.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace Erdos1017.Variation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A fixed bounded mean-zero witness to nonzero first variation remains
nonzero under operator-norm convergence. -/
theorem eventually_weightFirstVariation_ne_zero_of_tendsto
    (T : ℕ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : Tendsto T atTop (𝓝 S))
    (hregular : weightFirstVariation S ≠ 0) :
    ∀ᶠ n in atTop, weightFirstVariation (T n) ≠ 0 := by
  classical
  have ⟨f, hf⟩ : ∃ f : WeightDirections μ, weightFirstVariation S f ≠ 0 := by
    by_contra h
    push Not at h
    apply hregular
    apply LinearMap.ext
    intro f
    simpa using h f
  have hcontinuous : Continuous (fun R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ =>
      (2 : ℝ) * ⟪R (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫) := by
    fun_prop
  have hscalar : Tendsto (fun n => weightFirstVariation (T n) f) atTop
      (𝓝 (weightFirstVariation S f)) := by
    change Tendsto (fun n => (2 : ℝ) *
      ⟪T n (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫) atTop
      (𝓝 ((2 : ℝ) * ⟪S (Lp.const 2 μ (1 : ℝ)), directionToL2 f⟫))
    exact hcontinuous.continuousAt.tendsto.comp hT
  filter_upwards [hscalar.eventually (eventually_ne_nhds hf)] with n hn hzero
  exact hn (congrArg (fun L : WeightDirections μ →ₗ[ℝ] ℝ => L f) hzero)

end Erdos1017.Variation

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Operator-norm convergence of the actual adjacency operators preserves
regularity eventually. -/
theorem eventually_adjacency_regular_of_operator_tendsto
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (hOp : Tendsto (fun n => adjacencyOperator (W n)) atTop
      (𝓝 (adjacencyOperator V)))
    (hregular : Variation.weightFirstVariation (adjacencyOperator V) ≠ 0) :
    ∀ᶠ n in atTop,
      Variation.weightFirstVariation (adjacencyOperator (W n)) ≠ 0 :=
  Variation.eventually_weightFirstVariation_ne_zero_of_tendsto
    (fun n => adjacencyOperator (W n)) (adjacencyOperator V) hOp hregular

/-- A constant original adjacency row remains constant after an actual
measure-preserving reindexing. -/
theorem adjacency_row_pullback (W : Model Ω μ) (c : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, adjacencyKernel W x y ∂μ) = c)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) :
    ∀ᵐ x ∂μ,
      (∫ y, adjacencyKernel (W.pullback e he) x y ∂μ) = c := by
  filter_upwards [he.quasiMeasurePreserving.ae hrow] with x hx
  change (∫ y, adjacencyKernel W (e x) (e y) ∂μ) = c
  rw [he.integral_comp' (fun y => adjacencyKernel W (e x) y)]
  exact hx

/-- Regularity of an actually reindexed model implies regularity of its
original model, with no new multiplier or density assumption. -/
theorem adjacency_regular_of_pullback (W : Model Ω μ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (hregular : Variation.weightFirstVariation
      (adjacencyOperator (W.pullback e he)) ≠ 0) :
    Variation.weightFirstVariation (adjacencyOperator W) ≠ 0 := by
  intro hsingular
  have hrow := (Variation.kernel_weightFirstVariation_eq_zero_iff
    (adjacencyKernel W) (by norm_num) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W)).mp hsingular
  obtain ⟨c, hc⟩ := hrow
  have hsingularPull := (Variation.kernel_weightFirstVariation_eq_zero_iff
    (adjacencyKernel (W.pullback e he)) (by norm_num)
    (adjacencyKernel_measurable (W.pullback e he))
    (adjacencyKernel_bound (W.pullback e he))).mpr
      ⟨c, adjacency_row_pullback W c hc e he⟩
  exact hregular hsingularPull

/-- One common sequence of actual alignments transfers eventual regularity
back to the original models. -/
theorem eventually_adjacency_regular_original_of_aligned_operator_tendsto
    (W : ℕ → Model Ω μ) (V : Model Ω μ)
    (e : ℕ → Ω ≃ᵐ Ω) (he : ∀ n, MeasurePreserving (e n) μ μ)
    (hOp : Tendsto (fun n => adjacencyOperator ((W n).pullback (e n) (he n)))
      atTop (𝓝 (adjacencyOperator V)))
    (hregular : Variation.weightFirstVariation (adjacencyOperator V) ≠ 0) :
    ∀ᶠ n in atTop,
      Variation.weightFirstVariation (adjacencyOperator (W n)) ≠ 0 := by
  filter_upwards [eventually_adjacency_regular_of_operator_tendsto
    (fun n => (W n).pullback (e n) (he n)) V hOp hregular] with n hn
  exact adjacency_regular_of_pullback (W n) (e n) (he n) hn

end Erdos1017.CappedModel
