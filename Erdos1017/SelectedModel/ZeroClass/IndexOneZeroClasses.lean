module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Boundary zero classes of the feature law

Positive feature fibers are the countably many atoms of the pushforward law, and
those on the canonical boundary sphere give measurable disjoint zero classes
whose squares exhaust the kernel's zero pairs almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.KernelOperator

variable {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
  {μ : Measure Ω} [SFinite μ]

/-- Feature values whose actual fibers have positive latent measure. -/
def positiveFiberValues (μ : Measure Ω) (F : Ω → H) : Set H :=
  {v | 0 < μ {x | F x = v}}

theorem positiveFiberValues_countable [MeasurableSingletonClass H]
    (F : Ω → H) (hF : Measurable F) : (positiveFiberValues μ F).Countable :=
  Measure.countable_meas_level_set_pos hF

omit [SFinite μ] in
/-- Positive feature fibers are precisely the atoms of the pushforward law. -/
theorem mem_positiveFiberValues_iff_atom [MeasurableSingletonClass H]
    (F : Ω → H) (hF : Measurable F) (v : H) :
    v ∈ positiveFiberValues μ F ↔ 0 < (μ.map F) {v} := by
  rw [Measure.map_apply hF (measurableSet_singleton v)]
  rfl

section Metric

variable [MetricSpace H] [SecondCountableTopology H] [BorelSpace H]

/-- Outside a product-null set, equal features belong to a positive-measure
fiber. Equalities in zero-measure fibers contribute no pair mass. -/
theorem ae_equal_features_mem_positiveFiberValues (F : Ω → H) (hF : Measurable F) :
    ∀ᵐ p ∂μ.prod μ, F p.1 = F p.2 → F p.1 ∈ positiveFiberValues μ F := by
  have hA : MeasurableSet (positiveFiberValues μ F) :=
    (positiveFiberValues_countable F hF).measurableSet
  have heq : MeasurableSet {p : Ω × Ω | F p.1 = F p.2} :=
    measurableSet_eq_fun (hF.comp measurable_fst) (hF.comp measurable_snd)
  apply (Measure.ae_prod_iff_ae_ae (heq.imp (hF.comp measurable_fst hA))).mpr
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : F x ∈ positiveFiberValues μ F
  · exact Filter.Eventually.of_forall (fun _ _ => hx)
  · have hz : μ {y | F y = F x} = 0 := by
      apply le_antisymm _ zero_le
      exact le_of_not_gt hx
    have hne : ∀ᵐ y ∂μ, F y ≠ F x := by
      simpa only [ae_iff, not_not] using hz
    filter_upwards [hne] with y hy
    exact fun h => (hy h.symm).elim

end Metric

variable [NormedAddCommGroup H] [SecondCountableTopology H] [BorelSpace H]

/-- Positive-measure feature fibers on the canonical boundary sphere. -/
def boundaryFiberValues (μ : Measure Ω) (F : Ω → H) (R : ℝ) : Set H :=
  {v | v ∈ positiveFiberValues μ F ∧ ‖v‖ = R}

theorem boundaryFiberValues_countable (F : Ω → H) (hF : Measurable F) (R : ℝ) :
    (boundaryFiberValues μ F R).Countable :=
  (positiveFiberValues_countable F hF).mono (fun _ hv => hv.1)

/-- The zero pairs lie, almost everywhere, in the squares of the countably
many positive-measure boundary fibers. -/
theorem zero_pairs_iff_boundaryFiberValues
    (F : Ω → H) (hF : Measurable F) (K : Ω → Ω → ℝ) (R : ℝ)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      K p.1 p.2 = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2) :
    ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 ↔
      ∃ v ∈ boundaryFiberValues μ F R, F p.1 = v ∧ F p.2 = v := by
  filter_upwards [hzero, ae_equal_features_mem_positiveFiberValues F hF] with p hp hatom
  constructor
  · intro hK
    obtain ⟨hnorm, heq⟩ := hp.mp hK
    exact ⟨F p.1, ⟨hatom heq, hnorm⟩, rfl, heq.symm⟩
  · rintro ⟨v, hv, hx, hy⟩
    exact hp.mpr ⟨by simpa only [hx] using hv.2, hx.trans hy.symm⟩

/-- The actual positive feature-law atoms give measurable, disjoint zero
classes, and their squares exhaust the kernel's zero pairs almost everywhere. -/
theorem exists_countable_boundary_zero_classes
    (F : Ω → H) (hF : Measurable F) (K : Ω → Ω → ℝ) (R : ℝ)
    (hzero : ∀ᵐ p ∂μ.prod μ,
      K p.1 p.2 = 0 ↔ ‖F p.1‖ = R ∧ F p.1 = F p.2) :
    ∃ A : Set H, A.Countable ∧
      (∀ v ∈ A, MeasurableSet {x | F x = v} ∧
        0 < μ {x | F x = v} ∧ 0 < (μ.map F) {v} ∧ ‖v‖ = R) ∧
      A.Pairwise (fun v w => Disjoint {x | F x = v} {x | F x = w}) ∧
      (∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 ↔
        ∃ v ∈ A, F p.1 = v ∧ F p.2 = v) := by
  refine ⟨boundaryFiberValues μ F R, boundaryFiberValues_countable F hF R, ?_, ?_,
    zero_pairs_iff_boundaryFiberValues F hF K R hzero⟩
  · intro v hv
    exact ⟨hF (measurableSet_singleton v), hv.1,
      (mem_positiveFiberValues_iff_atom F hF v).mp hv.1, hv.2⟩
  · intro v _ w _ hne
    exact Set.disjoint_left.mpr (fun x hx hy => hne (hx.symm.trans hy))

end Erdos1017.KernelOperator
