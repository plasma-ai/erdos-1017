module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Tactic.Linarith

/-!
# Head price lower bound from the bare-head probability

For a finite independent law the bare-head probability is at least one minus the
expected remainder count, and the Bernoulli quadratic average pays the bare-head
slack; a valid signed two-head clique family then gets the union-bound
improvement, forcing the head price above the slope plus twice the intercept.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.TwoCenterHeadPrice

/-- The genuine empty-remainder probability of a finite independent law. -/
def bareProbability {m : ℕ} (p : Fin m → ℝ) : ℝ :=
  Selector.bernoulliWeight p (fun _ => false)

/-- The finite independent law retains all quadratic moments, including
its genuine empty outcome. No coefficient signs are imposed. -/
theorem bernoulli_quadratic_expectation {m : ℕ} (p : Fin m → ℝ) (D : Selector.Dual m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (∑ X : Selector.Selection m, Selector.bernoulliWeight p X * Selector.quadratic D X) =
      Selector.objective p D := by
  rw [← Selector.primal_dual_identity p (Selector.selectorWeight p)
    (Selector.bernoulli_selector_feasible p hp) D]
  apply Finset.sum_congr rfl
  intro X _
  by_cases hx : X = (fun _ => false)
  · simp only [hx, Selector.quadratic_empty, mul_zero]
  · simp only [Selector.selectorWeight, hx, ite_false]

/-- A finite union bound for independent omission probabilities, valid even
when the right-hand probability lower bound is nonpositive. -/
theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    1 - ∑ i ∈ s, p i ≤ ∏ i ∈ s, (1 - p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpi := hp i (Finset.mem_insert_self i s)
    have hps : ∀ j ∈ s, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hmul := mul_le_mul_of_nonneg_left (ih hps) (sub_nonneg.mpr hpi.2)
    have hsum := Finset.sum_nonneg (fun j hj => (hps j hj).1)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hpi.1 hsum]

/-- The bare-head probability is at least one minus the entire finite
remainder's expected count. -/
theorem bareProbability_lower_bound {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : 1 - ∑ i, p i ≤ bareProbability p := by
  simpa only [bareProbability, Selector.bernoulliWeight, Bool.false_eq_true, ite_false] using
    one_sub_sum_le_prod Finset.univ p (fun i _ => hp i)

/-- The actual finite Bernoulli average pays the old bare-head slack.
The constant T is the two-head charge and all other charges remain signed. -/
theorem quadratic_le_bare_slack {m : ℕ} (p : Fin m → ℝ) (D : Selector.Dual m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (T : ℝ)
    (htest : ∀ X : Selector.Selection m, T + Selector.quadratic D X ≤ 1) :
    T + Selector.objective p D ≤ 1 - bareProbability p * (1 - T) := by
  have hpoint (X : Selector.Selection m) : T + Selector.quadratic D X ≤
      1 - (if X = (fun _ => false) then 1 - T else 0) := by
    by_cases hx : X = (fun _ => false)
    · simp only [hx, Selector.quadratic_empty, add_zero, ite_true]
      linarith
    · simpa only [hx, ite_false, sub_zero] using htest X
  have havg := Finset.sum_le_sum (fun X (_ : X ∈ (Finset.univ : Finset (Selector.Selection m))) =>
    mul_le_mul_of_nonneg_left (hpoint X) (Selector.bernoulliWeight_nonneg p hp X))
  have hl : (∑ X : Selector.Selection m,
      Selector.bernoulliWeight p X * (T + Selector.quadratic D X)) = T + Selector.objective p D := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, Selector.bernoulli_total, one_mul, bernoulli_quadratic_expectation p D hp]
  have hr : (∑ X : Selector.Selection m, Selector.bernoulliWeight p X *
      (1 - (if X = (fun _ => false) then 1 - T else 0))) =
      1 - bareProbability p * (1 - T) := by
    simp only [mul_sub, mul_one, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Selector.bernoulli_total, bareProbability]
  rwa [hl, hr] at havg

/-- A valid signed two-head clique family has the explicit union-bound
head-price improvement, without an infinite product hypothesis. -/
theorem quadratic_le_union_slack {m : ℕ} (p : Fin m → ℝ) (D : Selector.Dual m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (T : ℝ)
    (htest : ∀ X : Selector.Selection m, T + Selector.quadratic D X ≤ 1) :
    T + Selector.objective p D ≤ 1 - (1 - ∑ i, p i) * (1 - T) := by
  have hT : T ≤ 1 := by simpa only [Selector.quadratic_empty, add_zero] using htest (fun _ => false)
  have hprod := mul_le_mul_of_nonneg_right (bareProbability_lower_bound p hp) (sub_nonneg.mpr hT)
  exact (quadratic_le_bare_slack p D hp T htest).trans (by linarith)

/-- The strict intercept and the two-head budget put the actual common
head mass above one third before any bare-head estimate is used. -/
theorem one_third_lt_of_intercept {t δ γ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ)
    (hintercept : δ / 4 < γ) (hbudget : γ ≤ 2 * δ * t ^ 2) : 1 / 3 < t := by
  by_contra hn
  have ht3 : t ≤ 1 / 3 := le_of_not_gt hn
  have hsq : t ^ 2 ≤ 1 / 9 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hδ.le
  nlinarith

/-- The actual union-slack budget and explicit intercept force the original
head price above the slope plus twice the intercept. -/
theorem head_price_lower_bound {t ell γ T : ℝ} (ht : 1 / 3 < t) (htop : t ≤ 1 / 2)
    (hell : ell < 1) (hT : T ≤ 1) (hintercept : (1 - ell) / 4 < γ)
    (hbudget : γ ≤ 2 * (1 - ell) * t ^ 2 - 2 * t * (3 * t - 1) * (1 - T)) :
    ell + 2 * γ ≤ T := by
  let δ := 1 - ell
  let e := 1 - T
  have hδ : 0 < δ := sub_pos.mpr hell
  have he : 0 ≤ e := sub_nonneg.mpr hT
  have htpos : 0 < t := by linarith
  have hfactor : 0 < t * (3 * t - 1) := mul_pos htpos (by linarith)
  have hsmall : e < δ / 2 := by
    by_contra hn
    have heδ : δ / 2 ≤ e := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left heδ hfactor.le
    have hquad : t - t ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hδquad := mul_le_mul_of_nonneg_left hquad hδ.le
    change (δ / 4 < γ) at hintercept
    change γ ≤ 2 * δ * t ^ 2 - 2 * t * (3 * t - 1) * e at hbudget
    nlinarith
  have hcoef : 0 < 2 * (δ - 3 * e) * (1 / 2 + t) + 2 * e := by
    by_cases hc : 0 ≤ δ - 3 * e
    · have hm := mul_nonneg hc (show 0 ≤ 1 / 2 + t by linarith)
      nlinarith
    · have hc : δ - 3 * e < 0 := lt_of_not_ge hc
      have hm := mul_nonneg (neg_pos.mpr hc).le (show 0 ≤ 1 / 2 - t by linarith)
      nlinarith
  have hmul := mul_nonneg (show 0 ≤ 1 / 2 - t by linarith) hcoef.le
  change γ ≤ 2 * δ * t ^ 2 - 2 * t * (3 * t - 1) * e at hbudget
  dsimp only [δ, e] at *
  nlinarith

end Erdos1017.TwoCenterHeadPrice
