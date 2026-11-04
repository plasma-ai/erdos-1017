module

public import Erdos1017.Models.Capped.CappedTransport
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteDensityRealization
public import Mathlib.Probability.Kernel.Representation

/-!
# Finite labels on an atomless class

Every finite probability law is realized by measurable labels on a positive
atomless class, with exact label masses equal to the class mass times the chosen
part weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A label map preserving the actual conditioned class law has exact
label masses under the original class restriction. -/
theorem measureReal_class_label_of_conditional_map {k : ℕ}
    (s : Set Ω) (hs : MeasurableSet s) (ρ : Measure (Fin k))
    (L : Ω → Fin k) (hL : MeasurePreserving L (ProbabilityTheory.cond μ s) ρ) (i : Fin k) :
    μ.real (s ∩ L ⁻¹' {i}) = μ.real s * ρ.real {i} := by
  have hpre := hL.measure_preimage (measurableSet_singleton i).nullMeasurableSet
  have hmass := ProbabilityTheory.cond_mul_eq_inter hs (L ⁻¹' {i}) μ
  rw [hpre] at hmass
  have hreal := congrArg ENNReal.toReal hmass
  change (ρ {i} * μ s).toReal = μ.real (s ∩ L ⁻¹' {i}) at hreal
  rw [ENNReal.toReal_mul] at hreal
  exact hreal.symm.trans (mul_comm _ _)

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

/-- Every finite probability law is realized by measurable labels on the
original positive atomless class. The exact original-class masses follow
from the conditioned law, without an independence assumption. -/
theorem exists_atomless_class_labels {k : ℕ}
    (s : Set Ω) (hs : MeasurableSet s) (hpos : 0 < μ s) (hk : 0 < k)
    (ρ : Measure (Fin k)) [IsProbabilityMeasure ρ] :
    ∃ L : Ω → Fin k, MeasurePreserving L (ProbabilityTheory.cond μ s) ρ ∧
      ∀ i : Fin k, μ.real (s ∩ L ⁻¹' {i}) = μ.real s * ρ.real {i} := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ s) := cond_isProbabilityMeasure hpos.ne'
  have hac : ProbabilityTheory.cond μ s ≪ μ := cond_absolutelyContinuous
  have : NullSingletonClass (ProbabilityTheory.cond μ s) :=
    ⟨fun x => hac (measure_singleton x)⟩
  obtain ⟨h, hh⟩ := exists_measurePreserving (μ := ProbabilityTheory.cond μ s)
    (ν := (volume : Measure unitInterval))
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨T, hT, hmap⟩ := Measure.exists_measurable_map_eq ρ
  have hT : MeasurePreserving T (volume : Measure unitInterval) ρ := ⟨hT, hmap⟩
  have hL := hT.comp hh
  exact ⟨T ∘ h, hL, fun i => measureReal_class_label_of_conditional_map s hs ρ _ hL i⟩

/-- The concrete finite part law is realized on the original class with
exact actual label mass equal to class mass times the chosen part weight. -/
theorem exists_atomless_class_labels_of_masses {k : ℕ}
    (s : Set Ω) (hs : MeasurableSet s) (hpos : 0 < μ s) (hk : 0 < k)
    (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    ∃ L : Ω → Fin k,
      MeasurePreserving L (ProbabilityTheory.cond μ s)
        (MultipartiteDensityRealization.labelLaw a ha hsum) ∧
      ∀ i : Fin k, μ.real (s ∩ L ⁻¹' {i}) = μ.real s * a i := by
  obtain ⟨L, hL, hmass⟩ := exists_atomless_class_labels s hs hpos hk
    (MultipartiteDensityRealization.labelLaw a ha hsum)
  refine ⟨L, hL, fun i => ?_⟩
  simpa only [Measure.real, MultipartiteDensityRealization.labelLaw_singleton,
    ENNReal.toReal_ofReal (ha i)] using hmass i

end Erdos1017.CappedModel
