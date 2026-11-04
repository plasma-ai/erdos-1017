module

public import Erdos1017.SelectedModel.Flows.MissingFlowDensity
public import Erdos1017.SelectedModel.Structure.IntegrableDegreeCone

/-!
# Reversing a product flow

`swapDensity` exchanges the two endpoints of a product flow: receipt and supply
swap, the direction is exactly negated, integrability, nonnegativity, mass and
quadratic energy are preserved, and a flow through strictly decreasing degree
pairs has negative degree slope.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Erdos1017.MissingFlow

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Reversing an actual product flow exchanges its two physical endpoints. -/
def swapDensity (q : Ω × Ω → ℝ) : Ω × Ω → ℝ := q ∘ Prod.swap

omit [IsFiniteMeasure μ] in
theorem receipt_swapDensity (q : Ω × Ω → ℝ) : receipt μ (swapDensity q) = supply μ q := rfl

omit [IsFiniteMeasure μ] in
theorem supply_swapDensity (q : Ω × Ω → ℝ) : supply μ (swapDensity q) = receipt μ q := rfl

omit [IsFiniteMeasure μ] in
/-- The reverse direction is exactly the negative original direction,
pointwise, without any integrability or symmetry premise. -/
theorem direction_swapDensity (q : Ω × Ω → ℝ) :
    direction μ (swapDensity q) = fun x => -direction μ q x := by
  funext x
  simp only [direction, receipt_swapDensity, supply_swapDensity]
  ring

theorem integrable_swapDensity {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ)) :
    Integrable (swapDensity q) (μ.prod μ) := hq.swap

theorem nonnegative_swapDensity {q : Ω × Ω → ℝ} (hq : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p) :
    ∀ᵐ p ∂μ.prod μ, 0 ≤ swapDensity q p :=
  Measure.measurePreserving_swap.quasiMeasurePreserving.ae hq

theorem integral_swapDensity (q : Ω × Ω → ℝ) :
    (∫ p, swapDensity q p ∂μ.prod μ) = ∫ p, q p ∂μ.prod μ :=
  integral_prod_swap q

omit [IsFiniteMeasure μ] in
/-- Reversal preserves the actual original unhalved quadratic energy. -/
theorem kernelEnergy_direction_swapDensity (K : Ω → Ω → ℝ) (q : Ω × Ω → ℝ) :
    KernelOperator.kernelEnergy (μ := μ) K (direction μ (swapDensity q)) =
      KernelOperator.kernelEnergy (μ := μ) K (direction μ q) := by
  rw [direction_swapDensity]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by ring)

/-- Every nonzero flow through strictly decreasing original degree pairs
has negative original degree slope, by actual reversal to an increasing flow. -/
theorem degree_pairing_neg {q : Ω × Ω → ℝ} (hq : Integrable q (μ.prod μ))
    (hqNonneg : ∀ᵐ p ∂μ.prod μ, 0 ≤ q p)
    (hqMass : 0 < ∫ p, q p ∂μ.prod μ)
    (g : Ω → ℝ) (hg : AEStronglyMeasurable g μ)
    {B : ℝ} (hgBound : ∀ᵐ x ∂μ, ‖g x‖ ≤ B)
    (horder : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → g p.1 < g p.2) :
    (∫ x, g x * direction μ q x ∂μ) < 0 := by
  have hmass : 0 < ∫ p, swapDensity q p ∂μ.prod μ := by
    rwa [integral_swapDensity]
  have hreverse : ∀ᵐ p ∂μ.prod μ, swapDensity q p ≠ 0 → g p.2 < g p.1 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae horder
  have hpos := degree_pairing_pos (integrable_swapDensity hq)
    (nonnegative_swapDensity hqNonneg) hmass g hg hgBound hreverse
  rw [direction_swapDensity] at hpos
  simp only [mul_neg, integral_neg] at hpos
  linarith

end Erdos1017.MissingFlow
