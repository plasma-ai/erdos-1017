module

public import Erdos1017.Models.Decorated.DecoratedAbsoluteContinuity
public import Erdos1017.Models.Capped.CappedDensityRestoration
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Same-support insertion

Reweighting present and absent outcomes separately (`supportWeight`) defines
same-support insertion, which inherits every imposed test through coordinatewise
absolute continuity, multiplies every color test vanishing on absent pairs by
the same present-outcome factor, and gains fraction `t` of the absent mass on
positive support.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open scoped Classical in
def presentFactor (a : ℝ) (t : unitInterval) : ℝ :=
  if 0 < a then (a + (t : ℝ) * (1 - a)) / a else 1

open scoped Classical in
def absentFactor (a : ℝ) (t : unitInterval) : ℝ :=
  if 0 < a then 1 - (t : ℝ) else 1

/-- Reweight present and absent outcomes separately. Positive support keeps
its conditional charge law; zero support is unchanged. -/
def supportWeight (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) (c : CappedColor) : ℝ :=
  presentFactor (W.moment CappedColor.adjacency p) t * CappedColor.adjacency c +
    absentFactor (W.moment CappedColor.adjacency p) t * (1 - CappedColor.adjacency c)

theorem measurable_supportWeight (W : Model Ω μ) (t : unitInterval) :
    Measurable (Function.uncurry (supportWeight W t)) := by
  have hA := (W.stronglyMeasurable_moment
    CappedColor.continuous_adjacency.measurable.stronglyMeasurable).measurable
  have hprod : Measurable (fun z : (Ω × Ω) × CappedColor =>
      W.moment CappedColor.adjacency z.1) := hA.comp measurable_fst
  unfold supportWeight presentFactor absentFactor Function.uncurry
  exact (((hprod.add (measurable_const.mul (measurable_const.sub hprod))).div hprod).ite
    (measurableSet_lt measurable_const hprod) measurable_const).mul
      (CappedColor.continuous_adjacency.measurable.comp measurable_snd) |>.add
    ((measurable_const.ite (measurableSet_lt measurable_const hprod) measurable_const).mul
      (measurable_const.sub (CappedColor.continuous_adjacency.measurable.comp measurable_snd)))

theorem presentFactor_nonneg (a : ℝ) (ha : a ∈ Icc 0 1) (t : unitInterval) :
    0 ≤ presentFactor a t := by
  unfold presentFactor
  split_ifs with h
  · exact div_nonneg (add_nonneg ha.1 (mul_nonneg t.property.1 (sub_nonneg.mpr ha.2))) h.le
  · norm_num

theorem absentFactor_nonneg (a : ℝ) (t : unitInterval) : 0 ≤ absentFactor a t := by
  unfold absentFactor
  split_ifs
  · exact sub_nonneg.mpr t.property.2
  · norm_num

theorem supportWeight_nonneg (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) (c : CappedColor) :
    0 ≤ supportWeight W t p c :=
  add_nonneg
    (mul_nonneg (presentFactor_nonneg _ (adjacency_moment_mem W p) t) (CappedColor.adjacency_mem c).1)
    (mul_nonneg (absentFactor_nonneg _ t) (sub_nonneg.mpr (CappedColor.adjacency_mem c).2))

theorem integrable_color_adjacency (W : Model Ω μ) (p : Ω × Ω) :
    Integrable CappedColor.adjacency (W.kernel p) :=
  Integrable.of_bound CappedColor.continuous_adjacency.measurable.stronglyMeasurable.aestronglyMeasurable
    1 (Filter.Eventually.of_forall (fun c => by
      rw [Real.norm_eq_abs, abs_of_nonneg (CappedColor.adjacency_mem c).1]
      exact (CappedColor.adjacency_mem c).2))

theorem integrable_supportWeight (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    Integrable (supportWeight W t p) (W.kernel p) := by
  exact ((integrable_color_adjacency W p).const_mul _).add
    (((integrable_const 1).sub (integrable_color_adjacency W p)).const_mul _)

/-- The pair-law reweighting has total mass exactly one, including both
boundary cases `A=0` and `A=1`. -/
theorem integral_supportWeight (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (∫ c, supportWeight W t p c ∂W.kernel p) = 1 := by
  unfold supportWeight
  have ha := integrable_color_adjacency W p
  rw [integral_add
    (f := fun c => presentFactor (W.moment CappedColor.adjacency p) t * CappedColor.adjacency c)
    (g := fun c => absentFactor (W.moment CappedColor.adjacency p) t * (1 - CappedColor.adjacency c))
    (ha.const_mul _) (((integrable_const 1).sub ha).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub (f := fun _ => (1 : ℝ)) (g := CappedColor.adjacency) (integrable_const 1) ha]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  change presentFactor (W.moment CappedColor.adjacency p) t * W.moment CappedColor.adjacency p +
    absentFactor (W.moment CappedColor.adjacency p) t * (1 - W.moment CappedColor.adjacency p) = 1
  unfold presentFactor absentFactor
  split_ifs with h
  · rw [div_mul_cancel₀ _ h.ne']
    ring
  · ring

/-- Actual same-support insertion, formed by an absolutely continuous
change of every conditional pair-color law. -/
def supportInsert (W : Model Ω μ) (t : unitInterval) : Model Ω μ where
  kernel := W.kernel.withDensity (fun p c => ENNReal.ofReal (supportWeight W t p c))
  markov := by
    constructor
    intro p
    rw [ProbabilityTheory.Kernel.withDensity_apply _
      (measurable_supportWeight W t).ennreal_ofReal]
    exact weightedMeasure_probability (integrable_supportWeight W t p)
      (Filter.Eventually.of_forall (supportWeight_nonneg W t p)) (integral_supportWeight W t p)
  symm := by
    filter_upwards [W.symm, W.moment_symm CappedColor.adjacency] with p hp hA
    rw [ProbabilityTheory.Kernel.withDensity_apply _ (measurable_supportWeight W t).ennreal_ofReal,
      ProbabilityTheory.Kernel.withDensity_apply _ (measurable_supportWeight W t).ennreal_ofReal, hp]
    congr 1
    funext c
    simp only [supportWeight, hA]

theorem supportInsert_absolutelyContinuous (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (supportInsert W t).kernel p ≪ W.kernel p :=
  ProbabilityTheory.Kernel.withDensity_absolutelyContinuous _ p

/-- Every imposed finite independent sampled test is inherited by actual
same-support insertion through coordinatewise absolute continuity. -/
theorem feasible_supportInsert (W : Model Ω μ) {r : ℕ} (hW : Feasible r W) (t : unitInterval) :
    Feasible r (supportInsert W t) := by
  intro n hn hnr
  filter_upwards [hW n hn hnr] with x hx
  exact (DecoratedKernel.pi_absolutelyContinuous_of_coordinates
    (fun p : CliquePair n => (supportInsert W t).kernel (x p.val.1, x p.val.2))
    (fun p : CliquePair n => W.kernel (x p.val.1, x p.val.2))
    (fun p => supportInsert_absolutelyContinuous W t (x p.val.1, x p.val.2))).ae_le hx

theorem moment_supportInsert (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω)
    (h : CappedColor → ℝ) :
    (supportInsert W t).moment h p = ∫ c, supportWeight W t p c * h c ∂W.kernel p := by
  change (∫ c, h c ∂(W.kernel.withDensity (fun p c =>
    ENNReal.ofReal (supportWeight W t p c))) p) = _
  rw [ProbabilityTheory.Kernel.withDensity_apply _ (measurable_supportWeight W t).ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun c => ENNReal.ofReal (supportWeight W t p c))
      (measurable_supportWeight W t).of_uncurry_left.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with c
  rw [ENNReal.toReal_ofReal (supportWeight_nonneg W t p c), smul_eq_mul]

/-- Every color test vanishing on absent pairs is multiplied by the same
present-outcome factor, so the conditional present law is retained. -/
theorem moment_supportInsert_of_absent_zero (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω)
    (h : CappedColor → ℝ) (hzero : h CappedColor.absent = 0) :
    (supportInsert W t).moment h p =
      presentFactor (W.moment CappedColor.adjacency p) t * W.moment h p := by
  rw [moment_supportInsert]
  have hpoint (c : CappedColor) : supportWeight W t p c * h c =
      presentFactor (W.moment CappedColor.adjacency p) t * h c := by
    by_cases hc : CappedColor.adjacency c = 1
    · simp [supportWeight, hc]
    · rw [color_eq_absent_of_not_present c hc]
      simp [supportWeight, hzero]
  simp_rw [hpoint]
  exact integral_const_mul _ _

/-- Positive support gains fraction `t` of its absent mass; zero support
stays exactly zero. -/
theorem adjacency_moment_supportInsert (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (supportInsert W t).moment CappedColor.adjacency p =
      if 0 < W.moment CappedColor.adjacency p then
        W.moment CappedColor.adjacency p + (t : ℝ) * (1 - W.moment CappedColor.adjacency p)
      else W.moment CappedColor.adjacency p := by
  rw [moment_supportInsert_of_absent_zero W t p _ CappedColor.adjacency_absent]
  unfold presentFactor
  split_ifs with h
  · exact div_mul_cancel₀ _ h.ne'
  · simp

theorem charge_moment_supportInsert (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω) :
    (supportInsert W t).moment CappedColor.charge p =
      presentFactor (W.moment CappedColor.adjacency p) t * W.moment CappedColor.charge p :=
  moment_supportInsert_of_absent_zero W t p _ CappedColor.charge_absent

theorem supportInsert_kernel_of_zero (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω)
    (hA : W.moment CappedColor.adjacency p = 0) :
    (supportInsert W t).kernel p = W.kernel p := by
  change W.kernel.withDensity (fun p c => ENNReal.ofReal (supportWeight W t p c)) p = _
  rw [ProbabilityTheory.Kernel.withDensity_apply _ (measurable_supportWeight W t).ennreal_ofReal]
  have heq : (fun c => ENNReal.ofReal (supportWeight W t p c)) = fun _ => 1 := by
    funext c
    simp [supportWeight, hA, presentFactor, absentFactor]
  rw [heq]
  simp

theorem supportInsert_kernel_of_one (W : Model Ω μ) (t : unitInterval) (p : Ω × Ω)
    (hA : W.moment CappedColor.adjacency p = 1) :
    (supportInsert W t).kernel p = W.kernel p := by
  have ha := integrable_color_adjacency W p
  have hz : (∫ c, 1 - CappedColor.adjacency c ∂W.kernel p) = 0 := by
    rw [integral_sub (f := fun _ => (1 : ℝ)) (g := CappedColor.adjacency) (integrable_const 1) ha]
    change (∫ _c, (1 : ℝ) ∂W.kernel p) - W.moment CappedColor.adjacency p = 0
    simp [hA]
  have haone : ∀ᵐ c ∂W.kernel p, CappedColor.adjacency c = 1 := by
    have he := (integral_eq_zero_iff_of_nonneg
      (fun c => sub_nonneg.mpr (CappedColor.adjacency_mem c).2) ((integrable_const 1).sub ha)).mp hz
    filter_upwards [he] with c hc
    change 1 - CappedColor.adjacency c = 0 at hc
    linarith
  change W.kernel.withDensity (fun p c => ENNReal.ofReal (supportWeight W t p c)) p = _
  rw [ProbabilityTheory.Kernel.withDensity_apply _ (measurable_supportWeight W t).ennreal_ofReal]
  have heq : (fun c => ENNReal.ofReal (supportWeight W t p c)) =ᵐ[W.kernel p] fun _ => 1 := by
    filter_upwards [haone] with c hc
    simp [supportWeight, hA, hc, presentFactor, absentFactor]
  rw [withDensity_congr_ae heq]
  simp

end Erdos1017.CappedModel
