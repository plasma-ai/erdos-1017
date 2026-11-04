module

public import Erdos1017.Models.Capped.CappedDensityRestoration

/-!
# Adjacency and charge operators of a capped model

The adjacency and charge kernels define symmetric integral operators
(`adjacencyOperator`, `chargeOperator`) matching the weighted adjacency and
charge integrals, and capped maximality supplies a regular multiplier with the
first-variation identity, stationary eigenvector and index bound
(`exists_regular_multiplier`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def adjacencyKernel (W : Model Ω μ) (x y : Ω) : ℝ := W.moment CappedColor.adjacency (x, y)

def chargeKernel (W : Model Ω μ) (x y : Ω) : ℝ := W.moment CappedColor.charge (x, y)

theorem adjacencyKernel_measurable (W : Model Ω μ) :
    AEStronglyMeasurable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) :=
  (W.stronglyMeasurable_moment CappedColor.continuous_adjacency.measurable.stronglyMeasurable).aestronglyMeasurable

theorem chargeKernel_measurable (W : Model Ω μ) :
    AEStronglyMeasurable (fun p : Ω × Ω => chargeKernel W p.1 p.2) (μ.prod μ) :=
  (W.stronglyMeasurable_moment CappedColor.continuous_charge.measurable.stronglyMeasurable).aestronglyMeasurable

theorem adjacencyKernel_bound (W : Model Ω μ) :
    ∀ᵐ p ∂μ.prod μ, ‖adjacencyKernel W p.1 p.2‖ ≤ 1 := by
  filter_upwards with p
  change ‖W.moment CappedColor.adjacency p‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W p).1]
  exact (adjacency_moment_mem W p).2

theorem chargeKernel_bound (W : Model Ω μ) :
    ∀ᵐ p ∂μ.prod μ, ‖chargeKernel W p.1 p.2‖ ≤ 3 := by
  filter_upwards with p
  have h := norm_integral_le_of_norm_le_const (μ := W.kernel p) (C := 3)
    (Filter.Eventually.of_forall (fun c : CappedColor => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩))
  simpa only [chargeKernel, DecoratedKernel.moment, probReal_univ, mul_one] using h

theorem adjacencyKernel_symm (W : Model Ω μ) :
    ∀ᵐ p ∂μ.prod μ, adjacencyKernel W p.1 p.2 = adjacencyKernel W p.2 p.1 := by
  filter_upwards [W.moment_symm CappedColor.adjacency] with p hp
  exact hp.symm

theorem chargeKernel_symm (W : Model Ω μ) :
    ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 = chargeKernel W p.2 p.1 := by
  filter_upwards [W.moment_symm CappedColor.charge] with p hp
  exact hp.symm

variable [IsProbabilityMeasure μ]

def adjacencyOperator (W : Model Ω μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  KernelOperator.operator (adjacencyKernel W) (by norm_num : (0 : ℝ) ≤ 1)
    (adjacencyKernel_measurable W) (adjacencyKernel_bound W)

def chargeOperator (W : Model Ω μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  KernelOperator.operator (chargeKernel W) (by norm_num : (0 : ℝ) ≤ 3)
    (chargeKernel_measurable W) (chargeKernel_bound W)

theorem adjacencyOperator_symmetric (W : Model Ω μ) :
    (adjacencyOperator W).toLinearMap.IsSymmetric :=
  KernelOperator.operator_symmetric _ _ _ _ (adjacencyKernel_symm W)

theorem chargeOperator_symmetric (W : Model Ω μ) : (chargeOperator W).toLinearMap.IsSymmetric :=
  KernelOperator.operator_symmetric _ _ _ _ (chargeKernel_symm W)

theorem weighted_adjacency_eq (W : Model Ω μ) (f : Lp ℝ 2 μ) :
    Variation.weightedPairIntegral (adjacencyKernel W) f = ⟪adjacencyOperator W f, f⟫ :=
  Variation.weightedPairIntegral_eq _ _ _ _ f

theorem weighted_charge_eq (W : Model Ω μ) (f : Lp ℝ 2 μ) :
    Variation.weightedPairIntegral (chargeKernel W) f = ⟪chargeOperator W f, f⟫ :=
  Variation.weightedPairIntegral_eq _ _ _ _ f

/-- Actual capped maximality supplies a regular multiplier together with
the first-variation identity, stationary eigenvector and index bound. -/
theorem exists_regular_multiplier [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hregular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0) :
    ∃ m ν : ℝ,
      Variation.weightFirstVariation (chargeOperator W) = m • Variation.weightFirstVariation (adjacencyOperator W) ∧
      (chargeOperator W - m • adjacencyOperator W) (Lp.const 2 μ (1 : ℝ)) = ν • Lp.const 2 μ (1 : ℝ) ∧
      FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (chargeOperator W - m • adjacencyOperator W)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (chargeOperator W - m • adjacencyOperator W)) ≤ 2 := by
  apply Variation.exists_stationary_shift_of_weight_local_max
    (adjacencyOperator W) (chargeOperator W)
    (KernelOperator.operator_isCompact _ _ _ _) (KernelOperator.operator_isCompact _ _ _ _)
    (adjacencyOperator_symmetric W) (chargeOperator_symmetric W)
    (KernelOperator.operator_range_bounded _ _ _ _) (KernelOperator.operator_range_bounded _ _ _ _)
    hregular 1 (by norm_num) le_rfl
  intro f hf hd
  have hd' : Variation.weightedPairIntegral (adjacencyKernel W) (Variation.vertexWeight f) =
      Variation.weightedPairIntegral (adjacencyKernel W) (Lp.const 2 μ (1 : ℝ)) := by
    simpa only [weighted_adjacency_eq, Variation.vertexWeight] using hd
  have hc := weight_local_max W hW f hf hd'
  change Variation.weightedPairIntegral (chargeKernel W) (Variation.vertexWeight f) ≤
    Variation.weightedPairIntegral (chargeKernel W) (Lp.const 2 μ (1 : ℝ)) at hc
  simpa only [weighted_charge_eq, Variation.vertexWeight] using hc

end Erdos1017.CappedModel
