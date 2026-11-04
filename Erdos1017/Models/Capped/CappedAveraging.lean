module

public import Erdos1017.Models.Capped.CappedMultilinearMoments
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Averaging the present charge of capped models

Averaging the present charge conditionally preserves every imposed clique test,
density and objective, so any capped optimizer admits an equally good optimizer
whose present charge is its own deterministic conditional mean
(`exists_averaged_maximizer`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def averagedPresentColor (W : Model Ω μ) (p : Ω × Ω) : CappedColor :=
  CappedColor.present (conditionalCharge W p) (conditionalCharge_mem W p)

def averagedPresence (W : Model Ω μ) (p : Ω × Ω) : unitInterval :=
  ⟨W.moment CappedColor.adjacency p, adjacency_moment_mem W p⟩

theorem measurable_averagedPresentColor (W : Model Ω μ) : Measurable (averagedPresentColor W) :=
  (measurable_const.prodMk (measurable_conditionalCharge W)).subtype_mk

theorem measurable_averagedPresence (W : Model Ω μ) : Measurable (averagedPresence W) := by
  exact (W.stronglyMeasurable_moment
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable.subtype_mk

/-- Retain the exact presence probability and replace the present charge
distribution by its conditional mean. -/
def averagedKernel (W : Model Ω μ) : Kernel (Ω × Ω) CappedColor where
  toFun p := bernoulliMeasure (averagedPresentColor W p) CappedColor.absent (averagedPresence W p)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [bernoulliMeasure_def, Measure.add_apply, Measure.smul_apply]
    have hA := measurable_averagedPresence W
    have hC := (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (measurable_averagedPresentColor W))
    have hc : Measurable (fun p => (unitInterval.toNNReal (averagedPresence W p) : ℝ≥0∞)) := by fun_prop
    have hd : Measurable (fun p =>
        (unitInterval.toNNReal (unitInterval.symm (averagedPresence W p)) : ℝ≥0∞)) := by fun_prop
    change Measurable (fun p => (unitInterval.toNNReal (averagedPresence W p) : ℝ≥0∞) *
      Measure.dirac (averagedPresentColor W p) s +
        (unitInterval.toNNReal (unitInterval.symm (averagedPresence W p)) : ℝ≥0∞) *
          Measure.dirac CappedColor.absent s)
    exact (hc.mul hC).add (hd.mul measurable_const)

instance (W : Model Ω μ) : IsMarkovKernel (averagedKernel W) := by
  constructor
  intro p
  change IsProbabilityMeasure (bernoulliMeasure (averagedPresentColor W p) CappedColor.absent
    (averagedPresence W p))
  infer_instance

/-- An actual probability-valued model with deterministic present charge,
having exactly the old adjacency and charge moments. -/
def averaged (W : Model Ω μ) : Model Ω μ where
  kernel := averagedKernel W
  markov := by infer_instance
  symm := by
    filter_upwards [W.moment_symm CappedColor.adjacency, conditionalCharge_symm W] with p hA hZ
    have ha : averagedPresence W p.swap = averagedPresence W p := Subtype.ext hA
    have hz : averagedPresentColor W p.swap = averagedPresentColor W p :=
      Subtype.ext (Prod.ext rfl hZ)
    change bernoulliMeasure _ _ _ = bernoulliMeasure _ _ _
    rw [ha, hz]

theorem adjacency_moment_averaged (W : Model Ω μ) (p : Ω × Ω) :
    (averaged W).moment CappedColor.adjacency p = W.moment CappedColor.adjacency p := by
  change (∫ c, CappedColor.adjacency c ∂bernoulliMeasure (averagedPresentColor W p)
    CappedColor.absent (averagedPresence W p)) = _
  rw [integral_bernoulliMeasure]
  simp [averagedPresentColor, averagedPresence, CappedColor.present, CappedColor.adjacency,
    CappedColor.absent, smul_eq_mul]

theorem charge_moment_averaged (W : Model Ω μ) (p : Ω × Ω) :
    (averaged W).moment CappedColor.charge p = W.moment CappedColor.charge p := by
  change (∫ c, CappedColor.charge c ∂bernoulliMeasure (averagedPresentColor W p)
    CappedColor.absent (averagedPresence W p)) = _
  rw [integral_bernoulliMeasure]
  simp only [averagedPresentColor, CappedColor.present, CappedColor.charge, CappedColor.absent,
    smul_eq_mul, mul_zero, add_zero]
  change W.moment CappedColor.adjacency p * conditionalCharge W p = W.moment CappedColor.charge p
  rw [charge_eq_conditionalCharge_mul]
  ring

theorem conditionalCharge_averaged (W : Model Ω μ) (p : Ω × Ω) :
    conditionalCharge (averaged W) p = conditionalCharge W p := by
  simp only [conditionalCharge, charge_moment_averaged, adjacency_moment_averaged]

theorem averaged_deterministic (W : Model Ω μ) (p : Ω × Ω) :
    ∀ᵐ c ∂(averaged W).kernel p,
      CappedColor.charge c = conditionalCharge W p * CappedColor.adjacency c := by
  have hs : MeasurableSet {c : CappedColor |
      CappedColor.charge c = conditionalCharge W p * CappedColor.adjacency c} :=
    measurableSet_eq_fun CappedColor.continuous_charge.measurable
      (measurable_const.mul CappedColor.continuous_adjacency.measurable)
  rw [ae_iff]
  change bernoulliMeasure (averagedPresentColor W p) CappedColor.absent (averagedPresence W p)
    {c | ¬(CappedColor.charge c = conditionalCharge W p * CappedColor.adjacency c)} = 0
  apply bernoulliMeasure_apply_of_notMem_of_notMem _ hs.compl
  · simp [averagedPresentColor, CappedColor.present, CappedColor.charge, CappedColor.adjacency]
  · simp

/-- Conditional averaging preserves every actually imposed clique test.
This uses the proved multilinear moment identity rather than an assumed
conditional averaging or convexity principle. -/
theorem feasible_averaged (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) : Feasible r (averaged W) := by
  intro n hn hnr
  filter_upwards [hW n hn hnr] with x hx
  apply ae_colorViolation_zero_of_moments
    (fun p : CliquePair n => W.kernel (x p.val.1, x p.val.2))
    (fun p : CliquePair n => (averaged W).kernel (x p.val.1, x p.val.2)) hx
    (fun p => adjacency_moment_averaged W (x p.val.1, x p.val.2))
    (fun p => charge_moment_averaged W (x p.val.1, x p.val.2))
    (fun p => conditionalCharge W (x p.val.1, x p.val.2))
    (fun p => averaged_deterministic W (x p.val.1, x p.val.2))

theorem density_averaged (W : Model Ω μ) : density (averaged W) = density W := by
  unfold density
  simp_rw [adjacency_moment_averaged]

theorem objective_averaged (W : Model Ω μ) : objective (averaged W) = objective W := by
  unfold objective
  simp_rw [charge_moment_averaged]

theorem averaged_isFixedMeasureMaximizer (W : Model Ω μ) {r : ℕ}
    (hW : IsFixedMeasureMaximizer r W) : IsFixedMeasureMaximizer r (averaged W) := by
  refine ⟨feasible_averaged W hW.1, ?_⟩
  intro V hV hd
  rw [density_averaged] at hd
  rw [objective_averaged]
  exact hW.2 V hV hd

theorem averaged_isMaximizer (W : Model Ω μ) {r : ℕ}
    (hW : IsMaximizer r W) : IsMaximizer r (averaged W) := by
  refine ⟨feasible_averaged W hW.1, ?_⟩
  intro ν hν hνμ V hV hd
  rw [density_averaged] at hd
  rw [objective_averaged]
  exact hW.2 ν hνμ V hV hd

/-- Any actual capped optimizer admits an actual equally good optimizer
whose present charge is its own deterministic conditional mean. -/
theorem exists_averaged_maximizer (W : Model Ω μ) {r : ℕ}
    (hW : IsFixedMeasureMaximizer r W) :
    ∃ V : Model Ω μ, IsFixedMeasureMaximizer r V ∧ density V = density W ∧
      objective V = objective W ∧ ∀ p, ∀ᵐ c ∂V.kernel p,
        CappedColor.charge c = conditionalCharge V p * CappedColor.adjacency c := by
  refine ⟨averaged W, averaged_isFixedMeasureMaximizer W hW, density_averaged W,
    objective_averaged W, ?_⟩
  intro p
  rw [conditionalCharge_averaged]
  exact averaged_deterministic W p

end Erdos1017.CappedModel
