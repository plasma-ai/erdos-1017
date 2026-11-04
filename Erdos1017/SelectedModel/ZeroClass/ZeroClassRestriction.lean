module

public import Erdos1017.Models.Capped.CappedModel
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditioning a decorated model on a class

This module defines `conditionOn`, conditioning a decorated model on a positive
latent class while keeping the original pair-color kernels, and shows that the
conditioned law is supported on the class, fixes a feature value on a feature
fiber, makes a positive boundary fiber a zero class, and has explicit density
and objective.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem conditioned_probability (s : Set Ω) (hpos : 0 < μ s) :
    IsProbabilityMeasure (ProbabilityTheory.cond μ s) :=
  cond_isProbabilityMeasure hpos.ne'

/-- Condition an actual decorated model on a positive latent class. The
conditional pair-color kernels remain exactly the original kernels. -/
def conditionOn (W : Model Ω μ) (s : Set Ω) (hpos : 0 < μ s) :
    Model Ω (ProbabilityTheory.cond μ s) := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) :=
    cond_isProbabilityMeasure hpos.ne'
  exact W.changeMeasure cond_absolutelyContinuous

@[simp] theorem conditionOn_kernel (W : Model Ω μ) (s : Set Ω) (hpos : 0 < μ s)
    (p : Ω × Ω) : (conditionOn W s hpos).kernel p = W.kernel p := rfl

@[simp] theorem conditionOn_moment (W : Model Ω μ) (s : Set Ω) (hpos : 0 < μ s)
    (f : CappedColor → ℝ) (p : Ω × Ω) :
    (conditionOn W s hpos).moment f p = W.moment f p := rfl

/-- Absolute continuity preserves each of the original sampled tests on
the normalized class probability space. -/
theorem feasible_conditionOn (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (s : Set Ω) (hpos : 0 < μ s) : Feasible r (conditionOn W s hpos) := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) :=
    cond_isProbabilityMeasure hpos.ne'
  exact feasible_changeMeasure W cond_absolutelyContinuous hW

theorem fullFeasible_conditionOn (W : Model Ω μ) (hW : ∀ r, Feasible r W)
    (s : Set Ω) (hpos : 0 < μ s) : ∀ r, Feasible r (conditionOn W s hpos) :=
  fun r => feasible_conditionOn W (hW r) s hpos

omit [IsProbabilityMeasure μ] in
/-- The conditioned latent law is supported on the actual class. -/
theorem ae_mem_conditioned (s : Set Ω) (hs : MeasurableSet s) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ s, x ∈ s := by
  have hac : ProbabilityTheory.cond μ s ≪ μ.restrict s :=
    Measure.smul_absolutelyContinuous
  exact hac.ae_le (ae_restrict_mem hs)

omit [IsProbabilityMeasure μ] in
/-- Conditioning on a measurable feature fiber fixes its feature value
almost everywhere under the actual conditioned law. -/
theorem ae_feature_eq_conditioned {H : Type*} [MeasurableSpace H]
    [MeasurableSingletonClass H] (F : Ω → H) (hF : Measurable F) (v : H) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ {x | F x = v}, F x = v :=
  ae_mem_conditioned {x | F x = v} (hF (measurableSet_singleton v))

/-- A positive boundary feature fiber is an actual zero class for the
conditioned kernel, using product absolute continuity. -/
theorem ae_zero_conditioned_featureFiber {H : Type*} [NormedAddCommGroup H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (F : Ω → H) (hF : Measurable F) (v : H)
    (hpos : 0 < μ {x | F x = v}) (K : Ω → Ω → ℝ) (R : ℝ) (hv : ‖v‖ = R)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      K p.1 p.2 = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2) :
    ∀ᵐ p ∂(ProbabilityTheory.cond μ {x | F x = v}).prod
      (ProbabilityTheory.cond μ {x | F x = v}), K p.1 p.2 = 0 := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ {x | F x = v}) :=
    conditioned_probability _ hpos
  have hclass := ae_feature_eq_conditioned (μ := μ) F hF v
  have hac : ProbabilityTheory.cond μ {x | F x = v} ≪ μ :=
    cond_absolutelyContinuous
  have hz := (hac.prod hac).ae_le hzero
  filter_upwards [hz, Measure.quasiMeasurePreserving_fst.ae hclass,
    Measure.quasiMeasurePreserving_snd.ae hclass] with p hp hx hy
  apply hp.mpr
  exact ⟨by simpa only [hx] using hv, hx.trans hy.symm⟩

/-- Normalized class-pair integrals use the square of the actual class
mass, with the same independent product law as the original model. -/
theorem integral_conditioned_prod (s : Set Ω) (f : Ω × Ω → ℝ) :
    (∫ p, f p ∂(ProbabilityTheory.cond μ s).prod (ProbabilityTheory.cond μ s)) =
      (∫ p in s ×ˢ s, f p ∂μ.prod μ) / (μ.real s) ^ 2 := by
  rw [ProbabilityTheory.cond, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_restrict, integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, Measure.real]
  ring

theorem density_conditionOn (W : Model Ω μ) (s : Set Ω) (hpos : 0 < μ s) :
    density (conditionOn W s hpos) =
      (∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ) /
        (2 * (μ.real s) ^ 2) := by
  unfold density
  rw [show (conditionOn W s hpos).moment CappedColor.adjacency =
    W.moment CappedColor.adjacency from rfl, integral_conditioned_prod]
  ring

theorem objective_conditionOn (W : Model Ω μ) (s : Set Ω) (hpos : 0 < μ s) :
    objective (conditionOn W s hpos) =
      (∫ p in s ×ˢ s, W.moment CappedColor.charge p ∂μ.prod μ) /
        (2 * (μ.real s) ^ 2) := by
  unfold objective
  rw [show (conditionOn W s hpos).moment CappedColor.charge =
    W.moment CappedColor.charge from rfl, integral_conditioned_prod]
  ring

end Erdos1017.CappedModel
