module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassTuran
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassRestriction

/-!
# Turán bound inside a zero class

This module defines `restrictedCliquePresence`, the clique-presence integral
with every sampled vertex restricted to one class, and shows that the normalized
internal adjacency density of a positive class obeys the Turán bound when its
next clique presence vanishes.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual clique-presence integral with every sampled latent vertex
restricted to one class. -/
def restrictedCliquePresence (W : Model Ω μ) (s : Set Ω) (m : ℕ) : ℝ :=
  ∫ x in Set.univ.pi (fun _ : Fin m => s),
    ∫ c, cliquePresence c ∂cliqueLaw W x ∂Measure.pi (fun _ : Fin m => μ)

/-- A zero restricted clique integral gives zero clique presence under the
actual normalized-class sampled color law. -/
theorem integral_conditionOn_cliquePresence_eq_zero (W : Model Ω μ)
    (s : Set Ω) (hpos : 0 < μ s)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ s)] (m : ℕ)
    (hzero : restrictedCliquePresence W s m = 0) :
    (∫ c, cliquePresence c ∂(sampledColorLaw (conditionOn W s hpos) m :
      Measure (CliquePair m → CappedColor))) = 0 := by
  let F : C(CliquePair m → CappedColor, ℝ) :=
    ⟨cliquePresence, continuous_cliquePresence m⟩
  let inner : (Fin m → Ω) → ℝ := fun x => ∫ c, F c ∂cliqueLaw W x
  have hsm : StronglyMeasurable inner := by
    change StronglyMeasurable (fun x => ∫ c, F c ∂cliqueKernel W m x)
    exact F.continuous.stronglyMeasurable.integral_kernel
  have hbound : ∀ x, ‖inner x‖ ≤ ‖F‖ := by
    intro x
    have h := norm_integral_le_of_norm_le_const
      (μ := cliqueLaw W x) (Filter.Eventually.of_forall fun c => F.norm_coe_le_norm c)
    simpa using h
  have hint : Integrable inner (Measure.pi (fun _ : Fin m => μ.restrict s)) :=
    Integrable.of_bound hsm.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall hbound)
  have hnonneg : ∀ x, 0 ≤ inner x :=
    fun x => integral_nonneg (fun c => cliquePresence_nonneg c)
  have hraw : (∫ x, inner x ∂Measure.pi (fun _ : Fin m => μ.restrict s)) = 0 := by
    rw [← Measure.restrict_pi_pi]
    exact hzero
  have hae : ∀ᵐ x ∂Measure.pi (fun _ : Fin m => μ.restrict s), inner x = 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hraw
  have hac : ProbabilityTheory.cond μ s ≪ μ.restrict s :=
    Measure.smul_absolutelyContinuous
  have hcond := (DecoratedKernel.pi_absolutelyContinuous hac m).ae_le hae
  have hcondint : (∫ x, inner x
      ∂Measure.pi (fun _ : Fin m => ProbabilityTheory.cond μ s)) = 0 :=
    integral_eq_zero_of_ae hcond
  change (∫ c, F c ∂(sampledColorLaw (conditionOn W s hpos) m :
    Measure (CliquePair m → CappedColor))) = 0
  rw [integral_sampledColorLaw]
  change (∫ x, inner x
    ∂Measure.pi (fun _ : Fin m => ProbabilityTheory.cond μ s)) = 0
  exact hcondint

/-- The normalized internal unhalved adjacency density of a positive
class obeys Turán when its next clique presence integral vanishes. -/
theorem internal_density_le_turan_of_zero_restricted_clique (W : Model Ω μ)
    (s : Set Ω) (hpos : 0 < μ s) (k : ℕ) (hk : 0 < k)
    (hzero : restrictedCliquePresence W s (k + 1) = 0) :
    (∫ p in s ×ˢ s, W.moment CappedColor.adjacency p ∂μ.prod μ) /
      (μ.real s) ^ 2 ≤ 1 - 1 / (k : ℝ) := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) :=
    cond_isProbabilityMeasure hpos.ne'
  have htest := integral_conditionOn_cliquePresence_eq_zero W s hpos (k + 1) hzero
  have ht := density_le_turan_of_zero_clique (conditionOn W s hpos) k hk htest
  calc
    _ = 2 * density (conditionOn W s hpos) := by
      rw [density_conditionOn]
      ring
    _ ≤ _ := ht

end Erdos1017.CappedModel
