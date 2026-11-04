module

public import Erdos1017.SelectedModel.Capped.CappedDeterministicTests
public import Erdos1017.Models.Capped.CappedGrowingLimit
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Capped decorated model from a scalar kernel

A supplied probability and bounded scalar charge define a decorated kernel with
independently sampled pair colors and deterministic present charge, on the same
carrier with the same density and objective; every imposed scalar clique test
yields the corresponding capped feasibility test (`fullFeasible_model`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.CappedModel.ScalarModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The present color records the supplied bounded scalar charge. -/
def presentColor (Z : Ω × Ω → Icc (-3 : ℝ) 1) (p : Ω × Ω) : CappedColor :=
  CappedColor.present (Z p) (Z p).property

theorem measurable_presentColor (Z : Ω × Ω → Icc (-3 : ℝ) 1) (hZ : Measurable Z) :
    Measurable (presentColor Z) :=
  (measurable_const.prodMk hZ.subtype_val).subtype_mk

/-- Independently sampled pair colors with the actual supplied probability
and a deterministic charge whenever the pair is present. -/
def kernel (P : Ω × Ω → unitInterval) (Z : Ω × Ω → Icc (-3 : ℝ) 1)
    (hP : Measurable P) (hZ : Measurable Z) : Kernel (Ω × Ω) CappedColor where
  toFun p := bernoulliMeasure (presentColor Z p) CappedColor.absent (P p)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [bernoulliMeasure_def, Measure.add_apply, Measure.smul_apply]
    have hC := (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (measurable_presentColor Z hZ))
    have hc : Measurable (fun p => (unitInterval.toNNReal (P p) : ℝ≥0∞)) := by fun_prop
    have hd : Measurable (fun p =>
        (unitInterval.toNNReal (unitInterval.symm (P p)) : ℝ≥0∞)) := by fun_prop
    change Measurable (fun p => (unitInterval.toNNReal (P p) : ℝ≥0∞) *
      Measure.dirac (presentColor Z p) s +
        (unitInterval.toNNReal (unitInterval.symm (P p)) : ℝ≥0∞) *
          Measure.dirac CappedColor.absent s)
    exact (hc.mul hC).add (hd.mul measurable_const)

instance (P : Ω × Ω → unitInterval) (Z : Ω × Ω → Icc (-3 : ℝ) 1)
    (hP : Measurable P) (hZ : Measurable Z) : IsMarkovKernel (kernel P Z hP hZ) := by
  constructor
  intro p
  change IsProbabilityMeasure (bernoulliMeasure (presentColor Z p) CappedColor.absent (P p))
  infer_instance

/-- The scalar Bernoulli model uses the original carrier and latent measure.
Only product-AE symmetry of the two supplied scalar inputs is needed. -/
def model (P : Ω × Ω → unitInterval) (Z : Ω × Ω → Icc (-3 : ℝ) 1)
    (hP : Measurable P) (hZ : Measurable Z)
    (hPsym : ∀ᵐ p ∂μ.prod μ, P p.swap = P p)
    (hZsym : ∀ᵐ p ∂μ.prod μ, Z p.swap = Z p) : Model Ω μ where
  kernel := kernel P Z hP hZ
  markov := by infer_instance
  symm := by
    filter_upwards [hPsym, hZsym] with p hp hz
    have hc : presentColor Z p.swap = presentColor Z p := by simp only [presentColor, hz]
    change bernoulliMeasure _ _ _ = bernoulliMeasure _ _ _
    rw [hp, hc]

variable (P : Ω × Ω → unitInterval) (Z : Ω × Ω → Icc (-3 : ℝ) 1)
  (hP : Measurable P) (hZ : Measurable Z)
  (hPsym : ∀ᵐ p ∂μ.prod μ, P p.swap = P p)
  (hZsym : ∀ᵐ p ∂μ.prod μ, Z p.swap = Z p)

theorem adjacency_moment (p : Ω × Ω) :
    (model P Z hP hZ hPsym hZsym).moment CappedColor.adjacency p = (P p : ℝ) := by
  change (∫ c, CappedColor.adjacency c ∂bernoulliMeasure (presentColor Z p)
    CappedColor.absent (P p)) = _
  rw [integral_bernoulliMeasure]
  simp [presentColor, CappedColor.present, CappedColor.adjacency, CappedColor.absent, smul_eq_mul]

theorem charge_moment (p : Ω × Ω) :
    (model P Z hP hZ hPsym hZsym).moment CappedColor.charge p = (P p : ℝ) * (Z p : ℝ) := by
  change (∫ c, CappedColor.charge c ∂bernoulliMeasure (presentColor Z p)
    CappedColor.absent (P p)) = _
  rw [integral_bernoulliMeasure]
  simp [presentColor, CappedColor.present, CappedColor.charge, CappedColor.absent, smul_eq_mul]

theorem shifted_moment (m : ℝ) (p : Ω × Ω) :
    shiftedMoment (model P Z hP hZ hPsym hZsym) m p = (P p : ℝ) * ((Z p : ℝ) - m) := by
  rw [shiftedMoment_eq, charge_moment, adjacency_moment]
  ring

theorem density_model : density (model P Z hP hZ hPsym hZsym) =
    (∫ p, (P p : ℝ) ∂μ.prod μ) / 2 := by
  unfold density
  simp_rw [adjacency_moment]

theorem objective_model : objective (model P Z hP hZ hPsym hZsym) =
    (∫ p, (P p : ℝ) * (Z p : ℝ) ∂μ.prod μ) / 2 := by
  unfold objective
  simp_rw [charge_moment]

/-- Every actual conditional sample has the prescribed present charge. -/
theorem deterministic_charge (p : Ω × Ω) :
    ∀ᵐ c ∂(model P Z hP hZ hPsym hZsym).kernel p,
      CappedColor.charge c = (Z p : ℝ) * CappedColor.adjacency c := by
  have hs : MeasurableSet {c : CappedColor |
      CappedColor.charge c = (Z p : ℝ) * CappedColor.adjacency c} :=
    measurableSet_eq_fun CappedColor.continuous_charge.measurable
      (measurable_const.mul CappedColor.continuous_adjacency.measurable)
  rw [ae_iff]
  change bernoulliMeasure (presentColor Z p) CappedColor.absent (P p)
    {c | ¬(CappedColor.charge c = (Z p : ℝ) * CappedColor.adjacency c)} = 0
  apply bernoulliMeasure_apply_of_notMem_of_notMem _ hs.compl
  · simp [presentColor, CappedColor.present, CappedColor.charge, CappedColor.adjacency]
  · simp

/-- A zero presence probability gives the actual absent color law. -/
theorem kernel_eq_dirac_of_zero (p : Ω × Ω) (hp : P p = 0) :
    (model P Z hP hZ hPsym hZsym).kernel p = Measure.dirac CappedColor.absent := by
  change bernoulliMeasure (presentColor Z p) CappedColor.absent (P p) = _
  rw [hp, bernoulliMeasure_zero]

/-- A sampled present pair can occur only at a nonzero supplied probability. -/
theorem present_implies_probability_ne_zero (p : Ω × Ω) :
    ∀ᵐ c ∂(model P Z hP hZ hPsym hZsym).kernel p,
      CappedColor.adjacency c = 1 → P p ≠ 0 := by
  by_cases hp : P p = 0
  · rw [kernel_eq_dirac_of_zero P Z hP hZ hPsym hZsym p hp]
    simp
  · exact Filter.Eventually.of_forall (fun _ _ => hp)

variable [IsProbabilityMeasure μ]

/-- Actual independent conditional colors satisfy the scalar support's
clique test. Both orientations of every sampled physical pair avoid the
same original exceptional sets. -/
theorem sampled_test_of_feasibleOrder (H : Ω → Ω → Bool)
    (hoff : ∀ᵐ p ∂μ.prod μ, H p.1 p.2 = false → P p = 0) {n : ℕ}
    (hcap : FiniteArity.FeasibleOrder μ H (fun x y => (Z (x, y) : ℝ)) n) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ᵐ c ∂cliqueLaw (model P Z hP hZ hPsym hZsym) x, violation c = 0 := by
  classical
  have hpair := FiniteArity.ae_all_pairs μ n
    (fun p => P p.swap = P p ∧ Z p.swap = Z p ∧ (H p.1 p.2 = false → P p = 0))
    (hPsym.and (hZsym.and hoff))
  filter_upwards [hcap, hpair] with x hx hp
  let W := model P Z hP hZ hPsym hZsym
  have hc : ∀ᵐ c ∂cliqueLaw W x, ∀ e : CliquePair n,
      CappedColor.charge (c e) = (Z (x e.val.1, x e.val.2) : ℝ) * CappedColor.adjacency (c e) ∧
      (CappedColor.adjacency (c e) = 1 → P (x e.val.1, x e.val.2) ≠ 0) := by
    change ∀ᵐ c ∂Measure.pi (fun e : CliquePair n => W.kernel (x e.val.1, x e.val.2)), _
    apply ae_all_iff.mpr
    intro e
    exact (measurePreserving_eval (fun e : CliquePair n => W.kernel (x e.val.1, x e.val.2))
      e).quasiMeasurePreserving.ae
      ((deterministic_charge P Z hP hZ hPsym hZsym _).and
        (present_implies_probability_ne_zero P Z hP hZ hPsym hZsym _))
  filter_upwards [hc] with c hc
  by_cases hzero : ∃ e, CappedColor.adjacency (c e) = 0
  · obtain ⟨e, he⟩ := hzero
    have hprod : (∏ f, CappedColor.adjacency (c f)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) he
    simp only [violation, hprod, mul_zero]
  · have hA (e : CliquePair n) : CappedColor.adjacency (c e) = 1 :=
      (CappedColor.adjacency_eq_zero_or_one (c e)).resolve_left (fun he => hzero ⟨e, he⟩)
    have hnz (i j : Fin n) (hij : i ≠ j) : P (x i, x j) ≠ 0 := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact (hc ⟨(i, j), h⟩).2 (hA _)
      · have hji := (hc ⟨(j, i), h⟩).2 (hA _)
        intro he
        apply hji
        exact (hp i j hij).1.trans he
    have hclique : FiniteArity.TupleClique H x := by
      intro i j hij
      apply Bool.eq_true_of_not_eq_false
      intro he
      exact hnz i j hij ((hp i j hij).2.2 he)
    have hcharge := hx hclique
    rw [tupleCharge_eq_upper _ x (fun i j hij => congrArg
      (fun z : Icc (-3 : ℝ) 1 => (z : ℝ)) (hp i j hij).2.1.symm)] at hcharge
    have hy (e : CliquePair n) : CappedColor.charge (c e) = (Z (x e.val.1, x e.val.2) : ℝ) := by
      simpa only [hA e, mul_one] using (hc e).1
    simp only [violation, hy, hA, Finset.prod_const_one, mul_one,
      max_eq_right (sub_nonpos.mpr hcharge)]

/-- Every genuinely imposed scalar clique test yields the corresponding
actual capped decorated feasibility tests. -/
theorem feasible_model (H : Ω → Ω → Bool)
    (hoff : ∀ᵐ p ∂μ.prod μ, H p.1 p.2 = false → P p = 0) {r : ℕ}
    (hcap : ∀ n, 2 ≤ n → n ≤ r →
      FiniteArity.FeasibleOrder μ H (fun x y => (Z (x, y) : ℝ)) n) :
    Feasible r (model P Z hP hZ hPsym hZsym) := by
  intro n hn hnr
  exact sampled_test_of_feasibleOrder P Z hP hZ hPsym hZsym H hoff (hcap n hn hnr)

/-- All actual scalar clique orders give full feasibility of the constructed
same-carrier probability-valued model. -/
theorem fullFeasible_model (H : Ω → Ω → Bool)
    (hoff : ∀ᵐ p ∂μ.prod μ, H p.1 p.2 = false → P p = 0)
    (hcap : ∀ n, 2 ≤ n → FiniteArity.FeasibleOrder μ H (fun x y => (Z (x, y) : ℝ)) n) :
    FullFeasible (model P Z hP hZ hPsym hZsym) := by
  intro r
  exact feasible_model P Z hP hZ hPsym hZsym H hoff (fun n hn _ => hcap n hn)

end Erdos1017.CappedModel.ScalarModel
