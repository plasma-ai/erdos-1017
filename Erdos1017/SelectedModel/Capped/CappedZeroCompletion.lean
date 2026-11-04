module

public import Erdos1017.SelectedModel.Capped.CappedScalarModel
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.SelectedModel.DiffuseCompletionFeasibility

/-!
# Completing missing pairs inside a set

Missing pairs inside `D` are inserted with probability `t` and charge `m` on the
original latent carrier; the density and objective increments are exact, the
shifted objective is preserved, and the completed scalar clique tests give
all-order feasibility.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.ZeroCompletion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The missing pairs inserted by completion inside D. -/
def missing (W : Model Ω μ) (m : ℝ) (D : Set Ω) [DecidablePred (· ∈ D)]
    (p : Ω × Ω) : ℝ :=
  if p.1 ∈ D ∧ p.2 ∈ D ∧ PhysicalRepresentative.adjacency W m p.1 p.2 = false then 1 else 0

/-- Old edges remain present; missing pairs inside D are inserted with
probability t, on the original latent carrier. -/
def probability (W : Model Ω μ) (m : ℝ) (D : Set Ω) [DecidablePred (· ∈ D)]
    (t : unitInterval) (p : Ω × Ω) : unitInterval :=
  if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1
  else if p.1 ∈ D ∧ p.2 ∈ D then t else 0

/-- Every possible new edge has the same recorded charge m. -/
def completedCharge (W : Model Ω μ) (m : ℝ) (D : Set Ω) [DecidablePred (· ∈ D)]
    (p : Ω × Ω) : ℝ :=
  FiniteArity.completeCharge (PhysicalRepresentative.adjacency W m)
    (PhysicalRepresentative.charge W m) D (-m) p.1 p.2

variable (W : Model Ω μ) (m : ℝ) (D : Set Ω) [DecidablePred (· ∈ D)]

theorem measurable_missing (hD : MeasurableSet D) : Measurable (missing W m D) :=
  measurable_const.ite ((hD.preimage measurable_fst).inter
    ((hD.preimage measurable_snd).inter
      (measurableSet_eq_fun (PhysicalRepresentative.measurable_adjacency W m) measurable_const)))
    measurable_const

theorem measurable_probability (hD : MeasurableSet D) (t : unitInterval) :
    Measurable (probability W m D t) :=
  measurable_const.ite
    (measurableSet_eq_fun (PhysicalRepresentative.measurable_adjacency W m) measurable_const)
    (measurable_const.ite ((hD.preimage measurable_fst).inter (hD.preimage measurable_snd))
      measurable_const)

theorem measurable_completedCharge (hD : MeasurableSet D) :
    Measurable (completedCharge W m D) :=
  FiniteArity.measurable_completeCharge _ (PhysicalRepresentative.measurable_adjacency W m)
    _ (PhysicalRepresentative.measurable_charge W m) D hD (-m)

theorem missing_mem (p : Ω × Ω) : missing W m D p ∈ Icc (0 : ℝ) 1 := by
  unfold missing
  split_ifs <;> norm_num

theorem probability_eq (t : unitInterval) (p : Ω × Ω) :
    (probability W m D t p : ℝ) =
      (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0) +
        (t : ℝ) * missing W m D p := by
  cases ha : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    by_cases hd : p.1 ∈ D ∧ p.2 ∈ D <;>
    simp [probability, missing, ha, hd]

theorem completedCharge_eq (p : Ω × Ω) :
    completedCharge W m D p = PhysicalRepresentative.charge W m p.1 p.2 + m * missing W m D p := by
  unfold completedCharge FiniteArity.completeCharge missing
  split_ifs with h
  · rw [PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 h.2.2]
    ring
  · ring

theorem completedCharge_mem (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) :
    completedCharge W m D p ∈ Icc (-3 : ℝ) 1 := by
  unfold completedCharge FiniteArity.completeCharge
  split_ifs
  · simpa using hm
  · exact PhysicalRepresentative.charge_mem_Icc W m p.1 p.2

theorem missing_symm (p : Ω × Ω) : missing W m D p.swap = missing W m D p := by
  simp only [missing, Prod.swap,
    PhysicalRepresentative.adjacency_symm W m p.2 p.1, and_left_comm]

theorem probability_symm (t : unitInterval) (p : Ω × Ω) :
    probability W m D t p.swap = probability W m D t p := by
  simp only [probability, Prod.swap,
    PhysicalRepresentative.adjacency_symm W m p.2 p.1, and_comm]

theorem completedCharge_symm (p : Ω × Ω) :
    completedCharge W m D p.swap = completedCharge W m D p := by
  rw [completedCharge_eq, completedCharge_eq, missing_symm]
  change PhysicalRepresentative.charge W m p.2 p.1 + _ = _
  rw [PhysicalRepresentative.charge_symm W m p.2 p.1]

theorem probability_zero_off_completed (t : unitInterval) (p : Ω × Ω)
    (hp : FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D p.1 p.2 = false) :
    probability W m D t p = 0 := by
  unfold FiniteArity.completeAdjacency at hp
  by_cases hd : p.1 ∈ D ∧ p.2 ∈ D
  · simp [hd] at hp
  · simp only [hd, ↓reduceIte] at hp
    simp [probability, hp, hd]

theorem probability_mul_charge (t : unitInterval) (p : Ω × Ω) :
    (probability W m D t p : ℝ) * completedCharge W m D p =
      PhysicalRepresentative.charge W m p.1 p.2 + m * (t : ℝ) * missing W m D p := by
  cases ha : PhysicalRepresentative.adjacency W m p.1 p.2
  · have hy := PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 ha
    by_cases hd : p.1 ∈ D ∧ p.2 ∈ D
    all_goals rw [completedCharge_eq]
    all_goals simp [probability, missing, ha, hd, hy] <;> ring
  · simp [probability, missing, completedCharge_eq, ha]

/-- The completed present charge lies in the original compact color box. -/
def charge (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) : Icc (-3 : ℝ) 1 :=
  ⟨completedCharge W m D p, completedCharge_mem W m D hm p⟩

theorem measurable_charge (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1) :
    Measurable (charge W m D hm) := (measurable_completedCharge W m D hD).subtype_mk

theorem charge_symm (hm : m ∈ Icc (-3 : ℝ) 1) (p : Ω × Ω) :
    charge W m D hm p.swap = charge W m D hm p :=
  Subtype.ext (completedCharge_symm W m D p)

/-- Actual random partial completion, retaining the same latent carrier,
measure and recorded multiplier. -/
def model (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1) (t : unitInterval) : Model Ω μ :=
  ScalarModel.model (probability W m D t) (charge W m D hm)
    (measurable_probability W m D hD t) (measurable_charge W m D hD hm)
    (Filter.Eventually.of_forall (probability_symm W m D t))
    (Filter.Eventually.of_forall (charge_symm W m D hm))

theorem adjacency_moment (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (t : unitInterval) (p : Ω × Ω) :
    (model W m D hD hm t).moment CappedColor.adjacency p =
      (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then 1 else 0) +
        (t : ℝ) * missing W m D p := by
  unfold model
  rw [ScalarModel.adjacency_moment]
  exact probability_eq W m D t p

theorem charge_moment (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (t : unitInterval) (p : Ω × Ω) :
    (model W m D hD hm t).moment CappedColor.charge p =
      PhysicalRepresentative.charge W m p.1 p.2 + m * (t : ℝ) * missing W m D p := by
  unfold model
  rw [ScalarModel.charge_moment]
  exact probability_mul_charge W m D t p

theorem adjacency_moment_ae_eq (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    ∀ᵐ p ∂μ.prod μ, (model W m D hD hm t).moment CappedColor.adjacency p =
      W.moment CappedColor.adjacency p + (t : ℝ) * missing W m D p := by
  filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hsupport] with p hp
  rw [adjacency_moment, hp]

theorem charge_moment_ae_eq (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    ∀ᵐ p ∂μ.prod μ, (model W m D hD hm t).moment CappedColor.charge p =
      W.moment CappedColor.charge p + m * (t : ℝ) * missing W m D p := by
  filter_upwards [PhysicalRepresentative.charge_ae_eq W m hsupport] with p hp
  rw [charge_moment, hp]
  rfl

theorem shifted_moment_ae_eq (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    ∀ᵐ p ∂μ.prod μ, shiftedMoment (model W m D hD hm t) m p = shiftedMoment W m p := by
  filter_upwards [adjacency_moment_ae_eq W m D hD hm hsupport t,
    charge_moment_ae_eq W m D hD hm hsupport t] with p ha hy
  rw [shiftedMoment_eq, shiftedMoment_eq, ha, hy]
  ring

theorem moments_at_zero (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ p ∂μ.prod μ,
      (model W m D hD hm 0).moment CappedColor.adjacency p = W.moment CappedColor.adjacency p ∧
      (model W m D hD hm 0).moment CappedColor.charge p = W.moment CappedColor.charge p := by
  filter_upwards [adjacency_moment_ae_eq W m D hD hm hsupport 0,
    charge_moment_ae_eq W m D hD hm hsupport 0] with p ha hy
  simpa using And.intro ha hy

variable [IsProbabilityMeasure μ]

/-- The density increase for unit completion, with the usual ordered-pair
factor one half. -/
def missingMass : ℝ := (∫ p, missing W m D p ∂μ.prod μ) / 2

theorem integrable_missing (hD : MeasurableSet D) :
    Integrable (missing W m D) (μ.prod μ) := by
  apply Integrable.of_bound (measurable_missing W m D hD).aestronglyMeasurable 1
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (missing_mem W m D p).1]
  exact (missing_mem W m D p).2

omit [IsProbabilityMeasure μ] in
theorem missingMass_nonneg : 0 ≤ missingMass W m D := by
  unfold missingMass
  exact div_nonneg (integral_nonneg (fun p => (missing_mem W m D p).1)) (by norm_num)

omit [IsProbabilityMeasure μ] in
/-- The completion coefficient is exactly half the actual missing-pair
region's real product measure. -/
theorem missingMass_eq_measure (hD : MeasurableSet D) :
    missingMass W m D =
      (μ.prod μ).real {p : Ω × Ω | p.1 ∈ D ∧ p.2 ∈ D ∧
        PhysicalRepresentative.adjacency W m p.1 p.2 = false} / 2 := by
  classical
  let s : Set (Ω × Ω) := {p | p.1 ∈ D ∧ p.2 ∈ D ∧
    PhysicalRepresentative.adjacency W m p.1 p.2 = false}
  have hs : MeasurableSet s := (hD.preimage measurable_fst).inter
    ((hD.preimage measurable_snd).inter
      (measurableSet_eq_fun (PhysicalRepresentative.measurable_adjacency W m) measurable_const))
  have he : missing W m D = s.indicator (fun _ => (1 : ℝ)) := by
    funext p
    simp [missing, s, Set.indicator]
  unfold missingMass
  rw [he]
  congr 1
  exact integral_indicator_one hs

/-- Actual all-order feasibility comes from the completed scalar clique
tests. Old-model feasibility alone is not an edge-insertion premise. -/
theorem fullFeasible_model (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hcap : ∀ n, 2 ≤ n → FiniteArity.FeasibleOrder μ
      (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D)
      (FiniteArity.completeCharge (PhysicalRepresentative.adjacency W m)
        (PhysicalRepresentative.charge W m) D (-m)) n)
    (t : unitInterval) : FullFeasible (model W m D hD hm t) := by
  apply ScalarModel.fullFeasible_model
    (probability W m D t) (charge W m D hm)
    (measurable_probability W m D hD t) (measurable_charge W m D hD hm)
    (Filter.Eventually.of_forall (probability_symm W m D t))
    (Filter.Eventually.of_forall (charge_symm W m D hm))
    (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D)
  · exact Filter.Eventually.of_forall (fun p hp => probability_zero_off_completed W m D t p hp)
  · exact hcap

/-- Exact density increment under the same original latent law. -/
theorem density_model (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    density (model W m D hD hm t) = density W + (t : ℝ) * missingMass W m D := by
  have ha := integrable_bounded_moment W CappedColor.adjacency
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable 1 (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2)
  unfold density missingMass
  rw [integral_congr_ae (adjacency_moment_ae_eq W m D hD hm hsupport t),
    integral_add ha ((integrable_missing W m D hD).const_mul _), integral_const_mul]
  ring

/-- Exact objective increment: each inserted edge has charge m. -/
theorem objective_model (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    objective (model W m D hD hm t) = objective W + m * (t : ℝ) * missingMass W m D := by
  have hy := integrable_bounded_moment W CappedColor.charge
    CappedColor.continuous_charge.measurable.stronglyMeasurable 3 (fun c => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(CappedColor.charge_mem c).1, (CappedColor.charge_mem c).2.trans (by norm_num)⟩)
  unfold objective missingMass
  rw [integral_congr_ae (charge_moment_ae_eq W m D hD hm hsupport t),
    integral_add hy ((integrable_missing W m D hD).const_mul _), integral_const_mul]
  ring

/-- The zero completion parameter preserves the original density and
objective, without asserting equality of the original color laws. -/
theorem density_objective_at_zero (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    density (model W m D hD hm 0) = density W ∧
      objective (model W m D hD hm 0) = objective W := by
  simp [density_model W m D hD hm hsupport, objective_model W m D hD hm hsupport]

/-- The original shifted objective is preserved by every completion
parameter under the original latent law. -/
theorem shifted_objective_model (hD : MeasurableSet D) (hm : m ∈ Icc (-3 : ℝ) 1)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) (t : unitInterval) :
    objective (model W m D hD hm t) - m * density (model W m D hD hm t) =
      objective W - m * density W := by
  rw [density_model W m D hD hm hsupport, objective_model W m D hD hm hsupport]
  ring

end Erdos1017.CappedModel.ZeroCompletion
