module

public import Erdos1017.FractionalLimit.Selector
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Signs of interior optimal selector duals

For an interior optimal selector dual, every pair coefficient is nonpositive and
every linear coefficient is at most one (`interior_optimal_signs`), and signed
dual feasibility bounds every relaxed selector by weak duality.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Selector

open scoped BigOperators

theorem update_expansion {m : ℕ} (p : Fin m → ℝ) (j k : Fin m) (t : ℝ) :
    Function.update p j t k = p k + if k = j then t - p j else 0 := by
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

/-- The objective is affine in each coordinate because the quadratic diagonal vanishes. -/
theorem objective_update {m : ℕ} (p : Fin m → ℝ) (D : Dual m) (j : Fin m) (t : ℝ) :
    objective (Function.update p j t) D = objective p D +
      (t - p j) * (D.alpha j + ∑ k, D.beta j k * p k) := by
  unfold objective
  simp_rw [update_expansion]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_irrel,
    Finset.mem_univ, ite_true, Finset.sum_const_zero, D.beta_diag]
  have hrow : (∑ k, D.beta j k * ((t - p j) * p k)) =
      (t - p j) * ∑ k, D.beta j k * p k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcol : (∑ k, D.beta k j * (p k * (t - p j))) =
      (t - p j) * ∑ k, D.beta j k * p k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [D.beta_symm k j]
    ring
  rw [hrow, hcol]
  ring

/-- Deleting a coordinate preserves the represented Boolean polynomial. -/
def delete {m : ℕ} (D : Dual m) (j : Fin m) : Dual m where
  alpha k := if k = j then 0 else D.alpha k
  beta k l := if k = j ∨ l = j then 0 else D.beta k l
  beta_symm k l := by
    by_cases hk : k = j <;> by_cases hl : l = j <;> simp [hk, hl, D.beta_symm]
  beta_diag k := by simp [D.beta_diag]

theorem delete_objective {m : ℕ} (p : Fin m → ℝ) (D : Dual m) (j : Fin m) :
    objective p (delete D j) = objective (Function.update p j 0) D := by
  unfold objective delete
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j <;> simp [hk, Function.update_of_ne]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hk : k = j <;> by_cases hl : l = j <;>
      simp [hk, hl, Function.update_of_ne]

theorem delete_feasible {m : ℕ} (D : Dual m) (hD : DualFeasible D) (j : Fin m) :
    DualFeasible (delete D j) := by
  intro X
  unfold quadratic
  rw [delete_objective]
  have heq : Function.update (fun k => bit (X k)) j 0 =
      fun k => bit (Function.update X j false k) := by
    funext k
    by_cases hk : k = j <;> simp [hk, bit, Function.update_of_ne]
  rw [heq]
  exact hD (Function.update X j false)

/-- An attained optimum cannot improve under deletion. -/
theorem optimal_marginal_nonneg {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hp : ∀ i, 0 < p i) (hD : DualOptimal p D) (j : Fin m) :
    0 ≤ D.alpha j + ∑ k, D.beta j k * p k := by
  have h := hD.2 (delete D j) (delete_feasible D hD.1 j)
  rw [delete_objective, objective_update] at h
  nlinarith [hp j]

/-- The interaction row with the coordinate being identified omitted. -/
def remainingRow {m : ℕ} (D : Dual m) (i j k : Fin m) : ℝ :=
  if k = i then 0 else D.beta j k

/-- Boolean identification replaces coordinate `j` by coordinate `i` and
uses `Xᵢ² = Xᵢ` to retain a quadratic polynomial with zero diagonal. -/
def identify {m : ℕ} (D : Dual m) (i j : Fin m) : Dual m where
  alpha k := (delete D j).alpha k + if k = i then D.alpha j + D.beta i j else 0
  beta k l := (delete D j).beta k l +
    (if k = i then remainingRow D i j l else 0) +
    (if l = i then remainingRow D i j k else 0)
  beta_symm k l := by rw [(delete D j).beta_symm]; ring
  beta_diag k := by
    by_cases hk : k = i <;> simp [hk, remainingRow, (delete D j).beta_diag]

theorem identify_objective {m : ℕ} (p : Fin m → ℝ) (D : Dual m) (i j : Fin m) :
    objective p (identify D i j) = objective p (delete D j) +
      (D.alpha j + D.beta i j) * p i + p i * ∑ k, remainingRow D i j k * p k := by
  unfold objective identify
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  have hrow : (∑ k, remainingRow D i j k * (p i * p k)) =
      p i * ∑ k, remainingRow D i j k * p k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcol : (∑ k, remainingRow D i j k * (p k * p i)) =
      p i * ∑ k, remainingRow D i j k * p k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hrow, hcol]
  ring

theorem remainingRow_sum {m : ℕ} (p : Fin m → ℝ) (D : Dual m) (i j : Fin m) :
    (∑ k, D.beta j k * p k) = D.beta i j * p i +
      ∑ k, remainingRow D i j k * p k := by
  have hterm (k : Fin m) : D.beta j k * p k =
      (if k = i then D.beta j i * p i else 0) + remainingRow D i j k * p k := by
    by_cases hk : k = i <;> simp [hk, remainingRow]
  calc
    (∑ k, D.beta j k * p k) = ∑ k,
        ((if k = i then D.beta j i * p i else 0) + remainingRow D i j k * p k) :=
      Finset.sum_congr rfl (fun k _ => hterm k)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [D.beta_symm j i]

/-- The precise product-objective gain from identification. -/
theorem identify_gain {m : ℕ} (p : Fin m → ℝ) (D : Dual m) (i j : Fin m) :
    objective p (identify D i j) - objective p D =
      (p i - p j) * (D.alpha j + ∑ k, remainingRow D i j k * p k) +
        D.beta i j * p i * (1 - p j) := by
  rw [identify_objective, delete_objective, objective_update, remainingRow_sum p D i j]
  ring

/-- Identification agrees with ordinary substitution on Boolean arguments. -/
theorem identify_quadratic {m : ℕ} (D : Dual m) (i j : Fin m)
    (X : Selection m) : quadratic (identify D i j) X =
      quadratic D (Function.update X j (X i)) := by
  let p : Fin m → ℝ := fun k => bit (X k)
  have hupdate : (fun k => bit (Function.update X j (X i) k)) =
      Function.update p j (p i) := by
    funext k
    by_cases hk : k = j <;> simp [hk, p, Function.update_of_ne]
  have hp : p i * p i = p i := by dsimp [p]; cases X i <;> norm_num [bit]
  unfold quadratic
  rw [hupdate, objective_update]
  change objective p (identify D i j) = _
  have hgain := identify_gain p D i j
  rw [remainingRow_sum p D i j]
  nlinarith [congrArg (fun z => D.beta i j * z) hp]

theorem identify_feasible {m : ℕ} (D : Dual m) (hD : DualFeasible D)
    (i j : Fin m) : DualFeasible (identify D i j) := by
  intro X
  rw [identify_quadratic D i j]
  exact hD (Function.update X j (X i))

/-- A positive pair coefficient gives a strict improvement after ordering its
two probabilities, provided deletion cannot improve the objective. -/
theorem identify_gain_pos {m : ℕ} (p : Fin m → ℝ) (D : Dual m) (i j : Fin m)
    (hi₀ : 0 < p i) (hi₁ : p i < 1) (hji : p j ≤ p i)
    (hbeta : 0 < D.beta i j)
    (hmarginal : 0 ≤ D.alpha j + ∑ k, D.beta j k * p k) :
    objective p D < objective p (identify D i j) := by
  rw [remainingRow_sum p D i j] at hmarginal
  have hproduct := mul_nonneg (sub_nonneg.mpr hji) hmarginal
  have hpositive := mul_pos (mul_pos hbeta hi₀) (sub_pos.mpr hi₁)
  have hgain := identify_gain p D i j
  nlinarith

/-- Every pair coefficient of an interior optimal dual is nonpositive. -/
theorem optimal_beta_nonpos {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hD : DualOptimal p D) :
    ∀ i j, D.beta i j ≤ 0 := by
  have hordered (i j : Fin m) (hji : p j ≤ p i) : D.beta i j ≤ 0 := by
    by_contra hbeta
    have hgain := identify_gain_pos p D i j (hp i).1 (hp i).2 hji
      (lt_of_not_ge hbeta) (optimal_marginal_nonneg p D (fun k => (hp k).1) hD j)
    have hopt := hD.2 (identify D i j) (identify_feasible D hD.1 i j)
    linarith
  intro i j
  rcases le_total (p j) (p i) with hji | hij
  · exact hordered i j hji
  · rw [D.beta_symm i j]
    exact hordered j i hij

/-- Singleton Boolean tests give the upper bound on each linear coefficient. -/
theorem feasible_alpha_le_one {m : ℕ} (D : Dual m) (hD : DualFeasible D) (i : Fin m) :
    D.alpha i ≤ 1 := by
  have h := hD (fun k => decide (k = i))
  simpa [quadratic, objective, bit, mul_ite, ite_mul, D.beta_diag] using h

/-- Interior optimal selector duals satisfy `0 ≤ α ≤ 1` and `β ≤ 0`.
This is conditional on an attained optimum and assumes no strong-duality theorem. -/
theorem interior_optimal_signs {m : ℕ} (p : Fin m → ℝ) (D : Dual m)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (hD : DualOptimal p D) :
    (∀ i, 0 ≤ D.alpha i ∧ D.alpha i ≤ 1) ∧ ∀ i j, D.beta i j ≤ 0 := by
  have hbeta := optimal_beta_nonpos p D hp hD
  refine ⟨?_, hbeta⟩
  intro i
  have hmarginal := optimal_marginal_nonneg p D (fun k => (hp k).1) hD i
  have hsum : (∑ k, D.beta i k * p k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    exact mul_nonpos_of_nonpos_of_nonneg (hbeta i k) (hp k).1.le
  exact ⟨by linarith, feasible_alpha_le_one D hD.1 i⟩

/-- Relaxed selectors have lower first loads and upper distinct pair loads. -/
def RelaxedPrimalFeasible {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ) : Prop :=
  (∀ X, 0 ≤ w X) ∧ w (fun _ => false) = 0 ∧
    (∀ i, p i ≤ ∑ X, w X * bit (X i)) ∧
    ∀ i j, i ≠ j → (∑ X, w X * (bit (X i) * bit (X j))) ≤ p i * p j

/-- Integrating a quadratic polynomial depends only on the first and pair loads. -/
theorem weighted_quadratic_identity {m : ℕ} (w : Selection m → ℝ) (D : Dual m) :
    (∑ X, w X * quadratic D X) =
      (∑ i, D.alpha i * ∑ X, w X * bit (X i)) +
      (∑ i, ∑ j, D.beta i j * ∑ X, w X * (bit (X i) * bit (X j))) / 2 := by
  unfold quadratic objective
  simp only [mul_add, mul_div, Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro X _
    ring
  · rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro X _
    ring

/-- Signed dual feasibility already bounds every relaxed selector; no relaxed
strong-duality theorem is needed for this direction. -/
theorem relaxed_weak_duality {m : ℕ} (p : Fin m → ℝ) (w : Selection m → ℝ)
    (D : Dual m) (hw : RelaxedPrimalFeasible p w) (hD : DualFeasible D)
    (halpha : ∀ i, 0 ≤ D.alpha i) (hbeta : ∀ i j, D.beta i j ≤ 0) :
    objective p D ≤ cost w := by
  have hfirst : (∑ i, D.alpha i * p i) ≤
      ∑ i, D.alpha i * ∑ X, w X * bit (X i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hw.2.2.1 i) (halpha i)
  have hpair : (∑ i, ∑ j, D.beta i j * (p i * p j)) ≤
      ∑ i, ∑ j, D.beta i j * ∑ X, w X * (bit (X i) * bit (X j)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simp [D.beta_diag]
    · exact mul_le_mul_of_nonpos_left (hw.2.2.2 i j hij) (hbeta i j)
  have hcharge : objective p D ≤ ∑ X, w X * quadratic D X := by
    rw [weighted_quadratic_identity]
    unfold objective
    linarith
  apply hcharge.trans
  apply Finset.sum_le_sum
  intro X _
  simpa using mul_le_mul_of_nonneg_left (hD X) (hw.1 X)

end Erdos1017.Selector
