module

public import Erdos1017.Models.Capped.CappedUniversalConfiguration
public import Erdos1017.Models.Capped.CappedTransport
public import Erdos1017.Models.Capped.CappedPairEdits
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Adjoining universal vertices to a capped model

An independent latent mark chooses universal vertices with probability `t` while
keeping the original law of the existing labels (`universalMeasure`), and the
resulting model (`adjoinUniversal`) is feasible with explicit adjacency and
charge moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An independent latent mark chooses universal vertices with probability
`t`, while retaining the original probability law of old vertex labels. -/
def universalMeasure (μ : Measure Ω) (t : unitInterval) : Measure (Ω × Bool) :=
  μ.prod (bernoulliMeasure true false t)

instance (t : unitInterval) : IsProbabilityMeasure (universalMeasure μ t) := by
  unfold universalMeasure
  infer_instance

omit [IsProbabilityMeasure μ] in
theorem universal_fst_measurePreserving (t : unitInterval) :
    MeasurePreserving Prod.fst (universalMeasure μ t) μ :=
  measurePreserving_fst

def universalLift (W : Model Ω μ) (t : unitInterval) : Model (Ω × Bool) (universalMeasure μ t) :=
  W.pullback Prod.fst (universal_fst_measurePreserving t)

def universalEdit (z : ((Ω × Bool) × (Ω × Bool)) × CappedColor) : CappedColor :=
  if z.1.1.2 = true ∨ z.1.2.2 = true then zeroChargePresent else z.2

theorem measurable_universalEdit : Measurable (universalEdit (Ω := Ω)) := by
  have hb1 : Measurable (fun z : ((Ω × Bool) × (Ω × Bool)) × CappedColor => z.1.1.2) := by fun_prop
  have hb2 : Measurable (fun z : ((Ω × Bool) × (Ω × Bool)) × CappedColor => z.1.2.2) := by fun_prop
  exact measurable_const.ite
    ((measurableSet_eq_fun hb1 measurable_const).union (measurableSet_eq_fun hb2 measurable_const))
    measurable_snd

/-- Actual universal zero-charge vertices, with their independent latent
probability law and pair-color kernel constructed explicitly. -/
def adjoinUniversal (W : Model Ω μ) (t : unitInterval) : Model (Ω × Bool) (universalMeasure μ t) :=
  (universalLift W t).edit universalEdit measurable_universalEdit
    (Filter.Eventually.of_forall (fun _ _ => by simp [universalEdit, or_comm]))

theorem feasible_adjoinUniversal (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) (t : unitInterval) :
    Feasible r (adjoinUniversal W t) := by
  have hbase := feasible_pullback W hW Prod.fst (universal_fst_measurePreserving t)
  intro n hn hnr
  filter_upwards [ae_all_subclique_tests (universalLift W t) hbase n] with x hx
  unfold cliqueLaw adjoinUniversal
  rw [DecoratedKernel.sampleLaw_edit]
  have hm : Measurable (fun c : CliquePair n → CappedColor =>
      fun p => universalEdit ((x p.val.1, x p.val.2), c p)) :=
    measurable_pi_iff.mpr (fun p =>
      measurable_universalEdit.comp (measurable_const.prodMk (measurable_pi_apply p)))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  filter_upwards [hx] with c hc
  change violation (universalConfiguration (fun i => (x i).2) c) = 0
  exact violation_universalConfiguration _ _ (fun k hk hkn e => hc k hk (hkn.trans hnr) e)

theorem moment_adjoinUniversal (W : Model Ω μ) (t : unitInterval)
    (p : (Ω × Bool) × (Ω × Bool)) (h : CappedColor → ℝ) (hh : StronglyMeasurable h) :
    (adjoinUniversal W t).moment h p =
      if p.1.2 = true ∨ p.2.2 = true then h zeroChargePresent else W.moment h (p.1.1, p.2.1) := by
  change (∫ c, h c ∂(universalLift W t).editKernel universalEdit p) = _
  rw [DecoratedKernel.editKernel_apply _ _ measurable_universalEdit,
    integral_map_of_stronglyMeasurable (φ := fun c => universalEdit (p, c))
      (measurable_universalEdit.comp measurable_prodMk_left) hh]
  by_cases hp : p.1.2 = true ∨ p.2.2 = true
  · simp only [universalEdit, hp, ↓reduceIte]
    simp
  · simp only [universalEdit, hp, ↓reduceIte]
    rfl

theorem adjacency_moment_adjoinUniversal (W : Model Ω μ) (t : unitInterval)
    (p : (Ω × Bool) × (Ω × Bool)) :
    (adjoinUniversal W t).moment CappedColor.adjacency p =
      if p.1.2 = true ∨ p.2.2 = true then 1 else W.moment CappedColor.adjacency (p.1.1, p.2.1) := by
  rw [moment_adjoinUniversal W t p _ CappedColor.continuous_adjacency.measurable.stronglyMeasurable,
    adjacency_zeroChargePresent]

theorem charge_moment_adjoinUniversal (W : Model Ω μ) (t : unitInterval)
    (p : (Ω × Bool) × (Ω × Bool)) :
    (adjoinUniversal W t).moment CappedColor.charge p =
      if p.1.2 = true ∨ p.2.2 = true then 0 else W.moment CappedColor.charge (p.1.1, p.2.1) := by
  rw [moment_adjoinUniversal W t p _ CappedColor.continuous_charge.measurable.stronglyMeasurable,
    charge_zeroChargePresent]

end Erdos1017.CappedModel
