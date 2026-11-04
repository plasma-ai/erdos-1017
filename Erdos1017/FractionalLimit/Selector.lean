module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite selector weights and signed quadratic duals

Finite selector weights and signed quadratic duals for the finite
multipartite comparison. Boolean assignments represent subsets of the
finite label set. No strong-duality or attainment assertion is assumed.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

abbrev Selection (m : ℕ) := Fin m → Bool

/-- The indicator of membership in a Boolean subset. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- Independent Bernoulli weights, including the empty outcome. -/
def bernoulliWeight {m : ℕ} (p : Fin m → ℝ) (X : Selection m) : ℝ :=
  ∏ i, if X i then p i else 1 - p i

/-- Product expectations factor, with no range assumption needed for the identity. -/
theorem bernoulli_product_expectation {m : ℕ} (p : Fin m → ℝ)
    (h : Fin m → Bool → ℝ) :
    (∑ X : Selection m, bernoulliWeight p X * ∏ i, h i (X i)) =
      ∏ i, ((1 - p i) * h i false + p i * h i true) := by
  simp only [bernoulliWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if b then p i else 1 - p i) * h i b)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Every finite collection of distinct labels has its exact product moment. -/
theorem bernoulli_moment {m : ℕ} (p : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ X : Selection m, bernoulliWeight p X * ∏ i ∈ S, bit (X i)) = ∏ i ∈ S, p i := by
  have h := bernoulli_product_expectation p (fun i b => if i ∈ S then bit b else 1)
  have hfactor : ∀ i : Fin m,
      (1 - p i) * (if i ∈ S then bit false else 1) +
        p i * (if i ∈ S then bit true else 1) = if i ∈ S then p i else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi, bit]
  simp only [hfactor] at h
  simpa only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.prod_const_one, mul_one] using h

theorem bernoulli_total {m : ℕ} (p : Fin m → ℝ) :
    ∑ X : Selection m, bernoulliWeight p X = 1 := by
  simpa using bernoulli_moment p ∅

theorem bernoulli_first_moment {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    (∑ X : Selection m, bernoulliWeight p X * bit (X i)) = p i := by
  simpa using bernoulli_moment p {i}

theorem bernoulli_pair_moment {m : ℕ} (p : Fin m → ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ X : Selection m, bernoulliWeight p X * (bit (X i) * bit (X j))) = p i * p j := by
  simpa [hij] using bernoulli_moment p {i, j}

theorem bernoulliWeight_nonneg {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (X : Selection m) : 0 ≤ bernoulliWeight p X := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

/-- Removing the empty Bernoulli outcome does not change positive-order moments. -/
def selectorWeight {m : ℕ} (p : Fin m → ℝ) (X : Selection m) : ℝ :=
  if X = (fun _ => false) then 0 else bernoulliWeight p X

theorem selector_first_moment {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    (∑ X : Selection m, selectorWeight p X * bit (X i)) = p i := by
  rw [← bernoulli_first_moment p i]
  apply Finset.sum_congr rfl
  intro X _
  by_cases hX : X = (fun _ => false)
  · simp [selectorWeight, hX, bit]
  · simp [selectorWeight, hX]

theorem selector_pair_moment {m : ℕ} (p : Fin m → ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ X : Selection m, selectorWeight p X * (bit (X i) * bit (X j))) = p i * p j := by
  rw [← bernoulli_pair_moment p i j hij]
  apply Finset.sum_congr rfl
  intro X _
  by_cases hX : X = (fun _ => false)
  · simp [selectorWeight, hX, bit]
  · simp [selectorWeight, hX]

/-- Exact first loads and distinct pair loads define the finite selector primal. -/
def PrimalFeasible {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ) : Prop :=
  (∀ X, 0 ≤ w X) ∧ w (fun _ => false) = 0 ∧
    (∀ i, ∑ X, w X * bit (X i) = p i) ∧
    ∀ i j, i ≠ j → ∑ X, w X * (bit (X i) * bit (X j)) = p i * p j

/-- The cost is total nonempty mass, since feasible weights vanish at the empty subset. -/
def cost {m : ℕ} (w : Selection m → ℝ) : ℝ := ∑ X, w X

theorem bernoulli_selector_feasible {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : PrimalFeasible p (selectorWeight p) := by
  refine ⟨?_, by simp [selectorWeight], selector_first_moment p, selector_pair_moment p⟩
  intro X
  unfold selectorWeight
  split_ifs
  · exact le_rfl
  · exact bernoulliWeight_nonneg p hp X

/-- The independent selector has cost at most one, including boundary parameters. -/
theorem bernoulli_selector_cost_le_one {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : cost (selectorWeight p) ≤ 1 := by
  rw [cost, ← bernoulli_total p]
  apply Finset.sum_le_sum
  intro X _
  unfold selectorWeight
  split_ifs
  · exact bernoulliWeight_nonneg p hp X
  · exact le_rfl

/-- A signed quadratic dual, with each unordered pair represented symmetrically. -/
structure Dual (m : ℕ) where
  alpha : Fin m → ℝ
  beta : Fin m → Fin m → ℝ
  beta_symm : ∀ i j, beta i j = beta j i
  beta_diag : ∀ i, beta i i = 0

/-- The factor `1/2` counts each unordered pair once. -/
def objective {m : ℕ} (p : Fin m → ℝ) (D : Dual m) : ℝ :=
  (∑ i, D.alpha i * p i) + (∑ i, ∑ j, D.beta i j * (p i * p j)) / 2

def quadratic {m : ℕ} (D : Dual m) (X : Selection m) : ℝ :=
  objective (fun i => bit (X i)) D

/-- The empty subset has charge zero, so including it introduces no extra constraint. -/
def DualFeasible {m : ℕ} (D : Dual m) : Prop :=
  ∀ X : Selection m, quadratic D X ≤ 1

/-- Optimality is a predicate; this definition asserts no existence or strong duality. -/
def DualOptimal {m : ℕ} (p : Fin m → ℝ) (D : Dual m) : Prop :=
  DualFeasible D ∧ ∀ D' : Dual m, DualFeasible D' → objective p D' ≤ objective p D

theorem quadratic_empty {m : ℕ} (D : Dual m) : quadratic D (fun _ => false) = 0 := by
  simp [quadratic, objective, bit]

/-- Exact primal moments identify the integrated dual charge with its product objective. -/
theorem primal_dual_identity {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ)
    (hw : PrimalFeasible p w) (D : Dual m) :
    (∑ X, w X * quadratic D X) = objective p D := by
  have hfirst : ∀ i, (∑ X, w X * (D.alpha i * bit (X i))) = D.alpha i * p i := by
    intro i
    simp_rw [mul_left_comm (w _) (D.alpha i), ← Finset.mul_sum]
    rw [hw.2.2.1 i]
  have hpair : ∀ i j,
      (∑ X, w X * (D.beta i j * (bit (X i) * bit (X j)))) = D.beta i j * (p i * p j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [D.beta_diag]
    · simp_rw [mul_left_comm (w _) (D.beta i j), ← Finset.mul_sum]
      rw [hw.2.2.2 i j hij]
  unfold quadratic objective
  simp only [mul_add, mul_div, Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => hfirst i)
  · rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hpair i j)

/-- Every signed feasible dual lower-bounds every exact selector cost. -/
theorem weak_duality {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ) (D : Dual m)
    (hw : PrimalFeasible p w) (hD : DualFeasible D) : objective p D ≤ cost w := by
  rw [← primal_dual_identity p w hw D]
  apply Finset.sum_le_sum
  intro X _
  simpa using mul_le_mul_of_nonneg_left (hD X) (hw.1 X)

/-- In particular, every feasible dual has objective at most one on the closed cube. -/
theorem objective_le_one {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hD : DualFeasible D) : objective p D ≤ 1 :=
  (weak_duality p (selectorWeight p) D (bernoulli_selector_feasible p hp) hD).trans
    (bernoulli_selector_cost_le_one p hp)

/-- Interior product targets give strictly positive weights to every nonempty subset. -/
theorem selectorWeight_pos {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (X : Selection m) (hX : X ≠ (fun _ => false)) :
    0 < selectorWeight p X := by
  simp only [selectorWeight, hX, ↓reduceIte]
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_pos.mpr (hp i).2

end Erdos1017.Selector
