module

public import Erdos1017.Models.Capped.CappedUniversalIntegrals

/-!
# Density and objective after adjoining universal mass

Adjoining universal mass fraction `t` gives an exact normalized density, and
since universal vertices have zero incident charge only the squared original
vertex mass scales the objective; canonical atomless transport realizes this
competitor on the original probability space.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exact normalized density after adjoining universal mass fraction `t`. -/
theorem density_adjoinUniversal (W : Model Ω μ) (t : unitInterval) :
    density (adjoinUniversal W t) =
      (1 - (t : ℝ)) ^ 2 * density W + (t : ℝ) - (t : ℝ) ^ 2 / 2 := by
  unfold density
  simp_rw [adjacency_moment_adjoinUniversal]
  rw [integral_universal_kernel t (W.moment CappedColor.adjacency)
    (W.stronglyMeasurable_moment CappedColor.continuous_adjacency.measurable.stronglyMeasurable)
    1 (fun p => by
      have hp := W.moment_mem_Icc CappedColor.continuous_adjacency.measurable.stronglyMeasurable
        CappedColor.adjacency_mem p
      rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
      exact hp.2) 1]
  ring

/-- Universal vertices have zero incident charge, so only the squared old
vertex mass scales the objective. -/
theorem objective_adjoinUniversal (W : Model Ω μ) (t : unitInterval) :
    objective (adjoinUniversal W t) = (1 - (t : ℝ)) ^ 2 * objective W := by
  unfold objective
  simp_rw [charge_moment_adjoinUniversal]
  rw [integral_universal_kernel t (W.moment CappedColor.charge)
    (W.stronglyMeasurable_moment CappedColor.continuous_charge.measurable.stronglyMeasurable)
    3 (fun p => by
      have h := norm_integral_le_of_norm_le_const (μ := W.kernel p) (C := 3)
        (Filter.Eventually.of_forall (fun c : CappedColor => by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
            (CappedColor.charge_mem c).2.trans (by norm_num : (1 : ℝ) ≤ 3)⟩))
      simpa only [DecoratedKernel.moment, probReal_univ, mul_one] using h) 0]
  ring

/-- Universal mass before normalization, expressed as its final fraction. -/
def universalFraction (u : ℝ) (hu : 0 ≤ u) : unitInterval :=
  ⟨u / (1 + u), div_nonneg hu (by linarith),
    (div_le_one (by linarith : (0 : ℝ) < 1 + u)).mpr (by linarith)⟩

theorem density_adjoinUniversal_mass (W : Model Ω μ) (u : ℝ) (hu : 0 ≤ u) :
    density (adjoinUniversal W (universalFraction u hu)) =
      (density W + u + u ^ 2 / 2) / (1 + u) ^ 2 := by
  rw [density_adjoinUniversal]
  change (1 - u / (1 + u)) ^ 2 * density W + u / (1 + u) - (u / (1 + u)) ^ 2 / 2 = _
  field_simp
  ring

theorem objective_adjoinUniversal_mass (W : Model Ω μ) (u : ℝ) (hu : 0 ≤ u) :
    objective (adjoinUniversal W (universalFraction u hu)) = objective W / (1 + u) ^ 2 := by
  rw [objective_adjoinUniversal]
  change (1 - u / (1 + u)) ^ 2 * objective W = _
  field_simp
  ring

/-- Canonical atomless transport realizes the universal-vertex competitor
back on the original fixed probability space, even when its old model used
another atomless probability law on the same latent type. -/
theorem exists_canonical_adjoinUniversal [StandardBorelSpace Ω] [NullSingletonClass μ]
    {ν : Measure Ω} [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (W : Model Ω ν) {r : ℕ} (hW : Feasible r W) (t : unitInterval) :
    ∃ V : Model Ω μ, Feasible r V ∧
      density V = (1 - (t : ℝ)) ^ 2 * density W + (t : ℝ) - (t : ℝ) ^ 2 / 2 ∧
      objective V = (1 - (t : ℝ)) ^ 2 * objective W := by
  have : NullSingletonClass (universalMeasure ν t) := by unfold universalMeasure; infer_instance
  obtain ⟨h, hh⟩ := exists_measurePreserving (Ω := Ω) (Λ := Ω × Bool)
    (μ := μ) (ν := universalMeasure ν t)
  refine ⟨(adjoinUniversal W t).pullback h hh,
    feasible_pullback _ (feasible_adjoinUniversal W hW t) h hh, ?_, ?_⟩
  · rw [density_pullback, density_adjoinUniversal]
  · rw [objective_pullback, objective_adjoinUniversal]

end Erdos1017.CappedModel
