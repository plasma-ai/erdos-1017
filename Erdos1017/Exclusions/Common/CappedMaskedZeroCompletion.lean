module

public import Erdos1017.SelectedModel.Capped.CappedZeroCompletion

/-!
# Completing the missing pairs of a measurable mask

This module defines the adjacency and charge obtained by inserting exactly the
pairs of a measurable mask (`maskAdjacency`, `maskCharge`), the masked missing
pairs and their mass, and proves full feasibility from the masked scalar tests,
the exact density increment, the objective, and that zero missing mass forces
completeness on the mask.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.FiniteArity

/-- Insert precisely the pairs in a measurable mask, retaining old edges. -/
def maskAdjacency {Ω : Type*} (A : Ω → Ω → Bool) (s : Set (Ω × Ω))
    [DecidablePred (· ∈ s)] (x y : Ω) : Bool :=
  if (x, y) ∈ s then true else A x y

/-- Only newly inserted masked edges receive the specified charge. -/
def maskCharge {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (s : Set (Ω × Ω)) [DecidablePred (· ∈ s)] (m : ℝ) (x y : Ω) : ℝ :=
  if (x, y) ∈ s ∧ A x y = false then m else Y x y

end Erdos1017.FiniteArity

namespace Erdos1017.CappedModel.MaskedZeroCompletion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual missing pairs selected by the mask, on the original law. -/
def missing (W : Model Ω μ) (m : ℝ) (s : Set (Ω × Ω)) [DecidablePred (· ∈ s)]
    (p : Ω × Ω) : ℝ :=
  if p ∈ s ∧ PhysicalRepresentative.adjacency W m p.1 p.2 = false then 1 else 0

def probability (W : Model Ω μ) (m : ℝ) (s : Set (Ω × Ω))
    [DecidablePred (· ∈ s)] (t : unitInterval) (p : Ω × Ω) : unitInterval :=
  if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else if p ∈ s then t else 0

def completedCharge (W : Model Ω μ) (m : ℝ) (s : Set (Ω × Ω))
    [DecidablePred (· ∈ s)] (p : Ω × Ω) : ℝ :=
  FiniteArity.maskCharge (PhysicalRepresentative.adjacency W m)
    (PhysicalRepresentative.charge W m) s m p.1 p.2

variable (W : Model Ω μ) (m : ℝ) (s : Set (Ω × Ω)) [DecidablePred (· ∈ s)]

theorem measurable_missing (hs : MeasurableSet s) : Measurable (missing W m s) :=
  measurable_const.ite (hs.inter (measurableSet_eq_fun
    (PhysicalRepresentative.measurable_adjacency W m) measurable_const)) measurable_const

theorem missing_mem (p : Ω × Ω) : missing W m s p ∈ Icc (0 : ℝ) 1 := by
  unfold missing
  split_ifs <;> norm_num

theorem measurable_probability (hs : MeasurableSet s) (t : unitInterval) :
    Measurable (probability W m s t) :=
  measurable_const.ite (measurableSet_eq_fun
    (PhysicalRepresentative.measurable_adjacency W m) measurable_const)
    (measurable_const.ite hs measurable_const)

theorem measurable_completedCharge (hs : MeasurableSet s) :
    Measurable (completedCharge W m s) :=
  measurable_const.ite (hs.inter (measurableSet_eq_fun
    (PhysicalRepresentative.measurable_adjacency W m) measurable_const))
    (PhysicalRepresentative.measurable_charge W m)

theorem completedCharge_mem (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) :
    completedCharge W m s p ∈ Icc (-3 : ℝ) 1 := by
  unfold completedCharge FiniteArity.maskCharge
  split_ifs
  · exact hm
  · exact PhysicalRepresentative.charge_mem_Icc W m p.1 p.2

def charge (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) : Icc (-3 : ℝ) 1 :=
  ⟨completedCharge W m s p, completedCharge_mem W m s hm p⟩

theorem probability_symm (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s)
    (t : unitInterval) (p : Ω × Ω) : probability W m s t p.swap = probability W m s t p := by
  rcases p with ⟨x, y⟩
  have hmask : (y, x) ∈ s ↔ (x, y) ∈ s := hsym (x, y)
  simp only [probability, Prod.swap, PhysicalRepresentative.adjacency_symm W m y x, hmask]

theorem completedCharge_symm (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s)
    (p : Ω × Ω) : completedCharge W m s p.swap = completedCharge W m s p := by
  rcases p with ⟨x, y⟩
  have hmask : (y, x) ∈ s ↔ (x, y) ∈ s := hsym (x, y)
  simp only [completedCharge, FiniteArity.maskCharge, Prod.swap,
    PhysicalRepresentative.adjacency_symm W m y x,
    PhysicalRepresentative.charge_symm W m y x, hmask]

theorem measurable_charge (hs : MeasurableSet s) (hm : m ∈ Icc (-3 : ℝ) 1) :
    Measurable (charge W m s hm) := (measurable_completedCharge W m s hs).subtype_mk

theorem charge_symm (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s)
    (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) :
    charge W m s hm p.swap = charge W m s hm p :=
  Subtype.ext (completedCharge_symm W m s hsym p)

/-- Actual Bernoulli partial insertion on an arbitrary symmetric mask.
Every new edge has the same recorded neutral shifted charge m. -/
def model (hs : MeasurableSet s) (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s)
    (hm : m ∈ Icc (-3 : ℝ) 1) (t : unitInterval) : Model Ω μ :=
  ScalarModel.model (probability W m s t) (charge W m s hm)
    (measurable_probability W m s hs t)
    (measurable_charge W m s hs hm)
    (Eventually.of_forall (probability_symm W m s hsym t))
    (Eventually.of_forall (charge_symm W m s hsym hm))

theorem probability_eq (t : unitInterval) (p : Ω × Ω) :
    (probability W m s t p : ℝ) =
      (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0) +
        (t : ℝ) * missing W m s p := by
  cases ha : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    by_cases hp : p ∈ s <;> simp [probability, missing, ha, hp]

theorem probability_mul_charge (t : unitInterval) (p : Ω × Ω) :
    (probability W m s t p : ℝ) * completedCharge W m s p =
      PhysicalRepresentative.charge W m p.1 p.2 + m * (t : ℝ) * missing W m s p := by
  cases ha : PhysicalRepresentative.adjacency W m p.1 p.2
  · have hy := PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 ha
    by_cases hp : p ∈ s
    all_goals simp [probability, missing, completedCharge, FiniteArity.maskCharge, ha, hp, hy]
    ring
  · simp [probability, missing, completedCharge, FiniteArity.maskCharge, ha]

theorem adjacency_moment_ae_eq (hs : MeasurableSet s)
    (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    ∀ᵐ p ∂μ.prod μ, (model W m s hs hsym hm t).moment CappedColor.adjacency p =
      W.moment CappedColor.adjacency p + (t : ℝ) * missing W m s p := by
  filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport] with p hp
  unfold model
  rw [ScalarModel.adjacency_moment, probability_eq, hp]

theorem charge_moment_ae_eq (hs : MeasurableSet s)
    (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    ∀ᵐ p ∂μ.prod μ, (model W m s hs hsym hm t).moment CappedColor.charge p =
      W.moment CappedColor.charge p + m * (t : ℝ) * missing W m s p := by
  filter_upwards [PhysicalRepresentative.charge_ae_eq W m hsupport] with p hp
  unfold model
  rw [ScalarModel.charge_moment]
  change (probability W m s t p : ℝ) * completedCharge W m s p = _
  rw [probability_mul_charge, hp]
  rfl

theorem shifted_moment_ae_eq (hs : MeasurableSet s)
    (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment (model W m s hs hsym hm t) m p = shiftedMoment W m p := by
  filter_upwards [adjacency_moment_ae_eq W m s hs hsym hm hsupport t,
    charge_moment_ae_eq W m s hs hsym hm hsupport t] with p ha hy
  rw [shiftedMoment_eq, shiftedMoment_eq, ha, hy]
  ring

variable [IsProbabilityMeasure μ]

/-- Half the original ordered missing-pair mass on precisely this mask. -/
def missingMass : ℝ := (∫ p, missing W m s p ∂μ.prod μ) / 2

theorem integrable_missing (hs : MeasurableSet s) : Integrable (missing W m s) (μ.prod μ) := by
  apply Integrable.of_bound (measurable_missing W m s hs).aestronglyMeasurable 1
  exact Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (missing_mem W m s p).1]
    exact (missing_mem W m s p).2)

omit [IsProbabilityMeasure μ] in
theorem missingMass_nonneg : 0 ≤ missingMass W m s :=
  div_nonneg (integral_nonneg (fun p => (missing_mem W m s p).1)) (by norm_num)

/-- Full feasibility follows from actual all-order masked scalar tests,
not merely from old-model feasibility. -/
theorem fullFeasible_model (hs : MeasurableSet s)
    (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hcap : ∀ n, 2 ≤ n → FiniteArity.FeasibleOrder μ
      (FiniteArity.maskAdjacency (PhysicalRepresentative.adjacency W m) s)
      (FiniteArity.maskCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) s m) n) (t : unitInterval) :
    FullFeasible (model W m s hs hsym hm t) := by
  apply ScalarModel.fullFeasible_model
    (probability W m s t) (charge W m s hm)
    (measurable_probability W m s hs t) (measurable_charge W m s hs hm)
    (Eventually.of_forall (probability_symm W m s hsym t))
    (Eventually.of_forall (charge_symm W m s hsym hm))
    (FiniteArity.maskAdjacency (PhysicalRepresentative.adjacency W m) s)
  · filter_upwards with p hp
    by_cases hps : p ∈ s
    · simp [FiniteArity.maskAdjacency, hps] at hp
    · simp only [FiniteArity.maskAdjacency, hps, ite_false] at hp
      simp [probability, hps, hp]
  · exact hcap

/-- The exact density increment under the same original latent law. -/
theorem density_model (hs : MeasurableSet s)
    (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    density (model W m s hs hsym hm t) = density W + (t : ℝ) * missingMass W m s := by
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  unfold density missingMass
  rw [integral_congr_ae (adjacency_moment_ae_eq W m s hs hsym hm hsupport t),
    integral_add ha ((integrable_missing W m s hs).const_mul _), integral_const_mul]
  ring

/-- Each new masked edge has the recorded original charge m. -/
theorem objective_model (hs : MeasurableSet s)
    (hsym : ∀ p : Ω × Ω, p.swap ∈ s ↔ p ∈ s) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    objective (model W m s hs hsym hm t) = objective W + m * (t : ℝ) * missingMass W m s := by
  have hy := integrable_bounded_moment W CappedColor.charge
    CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1,
        (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  unfold objective missingMass
  rw [integral_congr_ae (charge_moment_ae_eq W m s hs hsym hm hsupport t),
    integral_add hy ((integrable_missing W m s hs).const_mul _), integral_const_mul]
  ring

/-- Zero actual masked missing mass forces original completeness on
that mask, on one original product-AE event. -/
theorem ae_complete_of_missingMass_eq_zero (hs : MeasurableSet s)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hzero : missingMass W m s = 0) :
    ∀ᵐ p ∂μ.prod μ, p ∈ s → W.moment CappedColor.adjacency p = 1 := by
  have hi : (∫ p, missing W m s p ∂μ.prod μ) = 0 := by
    unfold missingMass at hzero
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun p => (missing_mem W m s p).1))
    (integrable_missing W m s hs)).mp hi
  filter_upwards [hz, PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport]
    with p hp hmoment hps
  cases hA : PhysicalRepresentative.adjacency W m p.1 p.2
  · simp [missing, hps, hA] at hp
  · simpa only [hA, ite_true] using hmoment

end Erdos1017.CappedModel.MaskedZeroCompletion
