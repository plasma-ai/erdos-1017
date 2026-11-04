module

public import Erdos1017.Multipartite.MultipartiteDensitySelection

/-!
# Count tests without a coefficient box

Inserting an unused head, restricting to finite dust cells and appending zero
heads preserve the count tests of any finite array regardless of coefficient
magnitudes or anchor-charge signs, and every finite homogeneous array passing
all count tests is bounded by the coefficient value.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.MultipartiteDust

/-- Inserting an unused head preserves all count tests without a coefficient
box premise. -/
theorem insertHead_tests {m : ℕ} (i : Fin (m + 1)) (C : Coefficients m)
    (hC : ∀ X k, charge C X k ≤ 1) : ∀ X k, charge (insertHead i C) X k ≤ 1 := by
  intro X k
  rw [DustCellBridge.charge_eq_objective, insertHead_objective]
  have h := hC (i.removeNth X) k
  rw [DustCellBridge.charge_eq_objective] at h
  exact h

/-- Finite dust-cell restriction uses only the literal anchored count tests.
The selector's signed dual has no coefficient sign or box restriction. -/
theorem restrictedDual_feasible_of_tests {m : ℕ} (C : Coefficients m)
    (hC : ∀ X k, charge C X k ≤ 1) (S : Finset (Fin m)) :
    Selector.DualFeasible (DustCellRestriction.restrictedDual C S) := by
  intro X
  let Y : Selector.Selection m := fun i => if i ∈ S then false else X i
  let k : ℕ := ∑ i, if i ∈ S then if X i then 1 else 0 else 0
  have hY : (fun i => Selector.bit (Y i)) =
      DustCellBridge.maskedMass S (fun i => Selector.bit (X i)) := by
    funext i
    by_cases hi : i ∈ S <;> simp [Y, DustCellBridge.maskedMass, Selector.bit, hi]
  have hk : (k : ℝ) = DustCellRestriction.cellMass S (fun i => Selector.bit (X i)) := by
    unfold k DustCellRestriction.cellMass
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> cases hX : X i <;>
      simp [DustCellRestriction.cell, Selector.bit, hi]
  have hdiag : (∑ i, DustCellRestriction.cell S i * Selector.bit (X i) ^ 2) =
      DustCellRestriction.cellMass S (fun i => Selector.bit (X i)) := by
    apply Finset.sum_congr rfl
    intro i _
    cases hX : X i <;> simp [Selector.bit, hX]
  have heq : Selector.quadratic (DustCellRestriction.restrictedDual C S) X = charge C Y k := by
    rw [Selector.quadratic, DustCellRestriction.restrictedDual_objective,
      DustCellBridge.charge_eq_objective, hY, hk, hdiag]
  rw [heq]
  exact hC Y k

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

/-- Appended zero heads preserve literal count feasibility of any finite
array, regardless of its coefficient magnitudes or anchor-charge signs. -/
theorem restrict_extendZero_tests_of_le {m : ℕ} (C : MultipartiteDust.Coefficients m)
    (hC : ∀ X k, MultipartiteDust.charge C X k ≤ 1) (N : ℕ) (hmN : m ≤ N) :
    ∀ X k, MultipartiteDust.charge (restrict N (extendZero C)) X k ≤ 1 := by
  induction N, hmN using Nat.le_induction with
  | base => simpa only [restrict_extendZero] using hC
  | @succ N hmN ih =>
    rw [restrict_extendZero_succ C N hmN]
    exact MultipartiteDust.insertHead_tests (Fin.last N) _ ih

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteDust

/-- Every arbitrary finite homogeneous array passing all count tests is
bounded by the actual coefficient value. Its dust penalty is nonnegative;
anchor charges may be negative and magnitudes may exceed one. -/
theorem objective_le_value_of_tests {m : ℕ} (C : Coefficients m)
    (hC : ∀ X k, charge C X k ≤ 1) (hpen : 0 ≤ penalty C)
    (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    objective p s C ≤ value p s := by
  have hcell (n : ℕ) (hn : 0 < n) (hsn : s ≤ n) :
      objective p s C ≤ Selector.value (DustPaddedCells.target p s n) := by
    let F := MultipartiteCountableDual.restrict (m + n) (MultipartiteCountableDual.extendZero C)
    let S := DustPaddedCells.cells m n
    have hF : ∀ X k, charge F X k ≤ 1 :=
      MultipartiteCountableDual.restrict_extendZero_tests_of_le C hC (m + n) (Nat.le_add_right _ _)
    have hdual := Selector.objective_le_value (DustPaddedCells.target p s n)
      (DustCellRestriction.restrictedDual F S) (DustPaddedCells.target_cube p hp s hs n hn hsn)
      (restrictedDual_feasible_of_tests F hF S)
    obtain ⟨hmask, hmass, hsquare⟩ := DustCellRestriction.uniform_cell_moments S
      (DustPaddedCells.cells_nonempty m n hn) (Fin.append p (fun _ : Fin n => 0)) s
      (DustPaddedCells.padded_zero p)
    change Selector.objective (fun i => Fin.append p (fun _ : Fin n => 0) i +
      s * Selector.uniformCellWeights S i) (DustCellRestriction.restrictedDual F S) ≤ _ at hdual
    rw [DustCellRestriction.restrictedDual_objective, hmask, hmass, hsquare] at hdual
    let q : ℕ → ℝ := fun k => if hk : k < m then p ⟨k, hk⟩ else 0
    have hqapp : (fun i : Fin (m + n) => q i.val) = Fin.append p (fun _ : Fin n => 0) := by
      funext i
      induction i using Fin.addCases with
      | left i => simp [q]
      | right i => simp [q, show ¬m + i.val < m by omega]
    have hqhead : (fun i : Fin m => q i.val) = p := by funext i; simp [q]
    have hobj := MultipartiteCountableDual.objective_restrict_extendZero_of_le C q s (m + n)
      (Nat.le_add_right _ _)
    rw [hqapp, hqhead] at hobj
    have hpenF : penalty F = penalty C := rfl
    change objective (Fin.append p (fun _ : Fin n => 0)) s F = objective p s C at hobj
    rw [hobj, hpenF] at hdual
    have hcorrection : 0 ≤ penalty C * (s ^ 2 / (S.card : ℝ)) / 2 := by positivity
    linarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (s ^ 2 / (2 * δ)) + 1)
  have hn0 : 0 < n := by
    have hnonneg : 0 ≤ max s (s ^ 2 / (2 * δ)) := (div_nonneg (sq_nonneg _) (by positivity)).trans
      (le_max_right _ _)
    exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hsn : s ≤ n := by linarith [le_max_left s (s ^ 2 / (2 * δ))]
  have hsmall : s ^ 2 / (2 * (n : ℝ)) ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have hdiv : s ^ 2 / (2 * δ) < n := by linarith [le_max_right s (s ^ 2 / (2 * δ))]
    have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * δ)).mp hdiv
    nlinarith
  have herror := (DustPaddedCells.finite_cell_value_error p hp s hs n hn0 hsn).2
  linarith [hcell n hn0 hsn]

end Erdos1017.MultipartiteDust
