module

public import Erdos1017.Exclusions.SmoothW.FreshIndependentStar
public import Erdos1017.Exclusions.Common.Physical.IndependentAtomCopyValues

/-!
# Density and objective of the fresh independent marker

The fresh independent marker has zero self density, adjacency row `1_D` and the
same charge row `1_D` (`density_marked`, `objective_marked`), with the
corresponding mass identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.FreshIndependentStar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
private theorem adjacency_real_eq_extension (A : Ω → Ω → Bool) (D : Set Ω)
    (z w : Ω × Bool) :
    (if adjacency A D z w = true then (1 : ℝ) else 0) =
      IndependentAtomCopy.extension
        (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0)
        (D.indicator (fun _ => (1 : ℝ))) z w := by
  cases hz : z.2 <;> cases hw : w.2 <;>
    by_cases hzD : z.1 ∈ D <;> by_cases hwD : w.1 ∈ D <;>
      simp [adjacency, IndependentAtomCopy.extension, hz, hw, hzD, hwD, Set.indicator]

/-- The fresh independent marker has zero self density and adjacency row `1_D`. -/
theorem density_marked (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (D : Set Ω) (hD : MeasurableSet D)
    (t : unitInterval) :
    FiniteCappedSamplingCost.physicalDensity (CappedModel.universalMeasure μ t)
        (adjacency A D) =
      (1 - (t : ℝ)) ^ 2 * FiniteCappedSamplingCost.physicalDensity μ A +
        (t : ℝ) * (1 - (t : ℝ)) *
          ∫ z, D.indicator (fun _ => (1 : ℝ)) z ∂μ := by
  unfold FiniteCappedSamplingCost.physicalDensity
  simp_rw [adjacency_real_eq_extension]
  have hK : StronglyMeasurable
      (fun p : Ω × Ω => if A p.1 p.2 = true then (1 : ℝ) else 0) :=
    (Measurable.ite (measurableSet_eq_fun hA measurable_const)
      measurable_const measurable_const).stronglyMeasurable
  have hf : StronglyMeasurable (D.indicator (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator hD).stronglyMeasurable
  rw [IndependentAtomCopy.integral_extension (μ := μ) t _ _ hK hf 1 1
    (fun p => by split_ifs <;> norm_num) (fun z => by
      by_cases hz : z ∈ D <;> simp [Set.indicator, hz])]
  ring

/-- The fresh independent marker has the same charge row `1_D`. -/
theorem objective_marked (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (D : Set Ω) (hD : MeasurableSet D)
    (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (t : unitInterval) :
    FiniteCappedSamplingCost.physicalObjective (CappedModel.universalMeasure μ t)
        (charge Y D) =
      (1 - (t : ℝ)) ^ 2 * FiniteCappedSamplingCost.physicalObjective μ Y +
        (t : ℝ) * (1 - (t : ℝ)) *
          ∫ z, D.indicator (fun _ => (1 : ℝ)) z ∂μ := by
  unfold FiniteCappedSamplingCost.physicalObjective
  change (∫ p, IndependentAtomCopy.extension (Function.uncurry Y)
    (D.indicator (fun _ => (1 : ℝ))) p.1 p.2
    ∂(CappedModel.universalMeasure μ t).prod (CappedModel.universalMeasure μ t)) / 2 = _
  have hf : StronglyMeasurable (D.indicator (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator hD).stronglyMeasurable
  rw [IndependentAtomCopy.integral_extension t _ _ hY.stronglyMeasurable hf B 1
    (fun p => hbound p.1 p.2) (fun z => by
      by_cases hz : z ∈ D <;> simp [Set.indicator, hz])]
  dsimp only [Function.uncurry]
  ring

theorem density_marked_mass (A : Ω → Ω → Bool)
    (hA : Measurable (Function.uncurry A)) (D : Set Ω) (hD : MeasurableSet D)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    FiniteCappedSamplingCost.physicalDensity
        (CappedModel.universalMeasure μ (CappedModel.universalFraction τ hτ))
        (adjacency A D) =
      (FiniteCappedSamplingCost.physicalDensity μ A +
        τ * ∫ z, D.indicator (fun _ => (1 : ℝ)) z ∂μ) / (1 + τ) ^ 2 := by
  rw [density_marked A hA D hD]
  simp only [CappedModel.universalFraction]
  field_simp [show 1 + τ ≠ 0 by linarith]
  ring

theorem objective_marked_mass (Y : Ω → Ω → ℝ)
    (hY : Measurable (Function.uncurry Y)) (D : Set Ω) (hD : MeasurableSet D)
    (B : ℝ) (hbound : ∀ x y, ‖Y x y‖ ≤ B)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    FiniteCappedSamplingCost.physicalObjective
        (CappedModel.universalMeasure μ (CappedModel.universalFraction τ hτ))
        (charge Y D) =
      (FiniteCappedSamplingCost.physicalObjective μ Y +
        τ * ∫ z, D.indicator (fun _ => (1 : ℝ)) z ∂μ) / (1 + τ) ^ 2 := by
  rw [objective_marked Y hY D hD B hbound]
  simp only [CappedModel.universalFraction]
  field_simp [show 1 + τ ≠ 0 by linarith]
  ring

end Erdos1017.FreshIndependentStar
