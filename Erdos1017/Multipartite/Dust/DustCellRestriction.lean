module

public import Erdos1017.Multipartite.Dust.DustCellBridge

/-!
# Restricting a dust dual to finite cells

A homogeneous dust dual restricts to separate independent cells
(`restrictedDual`), with the diagonal correction removing each cell's internal
demand; equal cells have square mass `s²/N`, and the two-sided finite-cell
approximation of the bounded homogeneous dust value follows.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.DustCellRestriction

open scoped BigOperators
open Selector DustCellBridge

/-- The symmetric finite dual represented by the head coordinates alone. -/
def headDual {m : ℕ} (C : MultipartiteDust.Coefficients m) : Dual m where
  alpha := MultipartiteDust.head C
  beta i j := -(if i < j then MultipartiteDust.pair C i j else
    if j < i then MultipartiteDust.pair C j i else 0)
  beta_symm i j := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · rfl
    · simp [h, not_lt_of_gt h]
  beta_diag i := by simp

theorem headDual_objective {m : ℕ} (C : MultipartiteDust.Coefficients m) (p : Fin m → ℝ) :
    objective p (headDual C) = MultipartiteDust.objective p 0 C := by
  unfold objective
  rw [symmetric_half_sum]
  have hterm (i j : Fin m) : (headDual C).beta i j * (if i < j then 1 else 0) * p i * p j =
      -(MultipartiteDust.pair C i j * (if i < j then 1 else 0) * p i * p j) := by
    by_cases h : i < j <;> simp [headDual, h]
  simp_rw [hterm]
  simp [headDual, MultipartiteDust.objective, Finset.sum_neg_distrib, sub_eq_add_neg]

def cell {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : ℝ := if i ∈ S then 1 else 0

def incidence {m : ℕ} (C : MultipartiteDust.Coefficients m) (S : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ S then 0 else MultipartiteDust.incident C i

/-- Restrict a homogeneous dust dual to separate independent cells.
The diagonal correction removes the internal demand of each individual cell. -/
def restrictedDual {m : ℕ} (C : MultipartiteDust.Coefficients m) (S : Finset (Fin m)) : Dual m where
  alpha i := (maskedDual (headDual C) S).alpha i + MultipartiteDust.linear C * cell S i
  beta i j := (maskedDual (headDual C) S).beta i j - incidence C S i * cell S j -
    cell S i * incidence C S j - MultipartiteDust.penalty C * cell S i * cell S j +
    if i = j then MultipartiteDust.penalty C * cell S i else 0
  beta_symm i j := by
    rw [(maskedDual (headDual C) S).beta_symm]
    by_cases h : i = j
    · subst j
      rfl
    · simp only [h, Ne.symm h, ↓reduceIte]
      ring
  beta_diag i := by
    rw [(maskedDual (headDual C) S).beta_diag]
    by_cases h : i ∈ S <;> simp [incidence, cell, h]

def cellMass {m : ℕ} (S : Finset (Fin m)) (p : Fin m → ℝ) : ℝ := ∑ i, cell S i * p i

/-- Exact restriction objective, before using Boolean or equal-cell moments. -/
theorem restrictedDual_objective {m : ℕ} (C : MultipartiteDust.Coefficients m)
    (S : Finset (Fin m)) (p : Fin m → ℝ) :
    objective p (restrictedDual C S) =
      MultipartiteDust.objective (maskedMass S p) (cellMass S p) C +
        MultipartiteDust.penalty C * (∑ i, cell S i * p i ^ 2) / 2 := by
  have hrow : (∑ i, ∑ j, incidence C S i * cell S j * (p i * p j)) =
      (∑ i, incidence C S i * p i) * cellMass S p := by
    unfold cellMass
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hcol : (∑ i, ∑ j, cell S i * incidence C S j * (p i * p j)) =
      (∑ i, incidence C S i * p i) * cellMass S p := by
    rw [Finset.sum_comm]
    unfold cellMass
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hquad : (∑ i, ∑ j, MultipartiteDust.penalty C * cell S i * cell S j * (p i * p j)) =
      MultipartiteDust.penalty C * (cellMass S p) ^ 2 := by
    unfold cellMass
    rw [pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hdiag : (∑ i, ∑ j, (if i = j then MultipartiteDust.penalty C * cell S i else 0) * (p i * p j)) =
      MultipartiteDust.penalty C * ∑ i, cell S i * p i ^ 2 := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hlinear : (∑ i, MultipartiteDust.linear C * cell S i * p i) =
      MultipartiteDust.linear C * cellMass S p := by
    unfold cellMass
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hincidence : (∑ i, incidence C S i * p i) =
      ∑ i, MultipartiteDust.incident C i * maskedMass S p i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i ∈ S <;> simp [incidence, maskedMass, h]
  have hhead := maskedDual_objective (headDual C) S p
  rw [headDual_objective] at hhead
  unfold objective at hhead
  unfold objective restrictedDual
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hrow, hcol, hquad, hdiag, hlinear, hincidence]
  unfold MultipartiteDust.objective at *
  simp only [mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Finset.sum_const_zero] at hhead
  rw [← Finset.sum_mul]
  linarith

/-- Every all-count homogeneous constraint restricts to the finite cell subsets. -/
theorem restrictedDual_feasible {m : ℕ} (C : MultipartiteDust.Coefficients m)
    (hC : C ∈ MultipartiteDust.feasible m) (S : Finset (Fin m)) :
    DualFeasible (restrictedDual C S) := by
  intro X
  let Y : Selection m := fun i => if i ∈ S then false else X i
  let k : ℕ := ∑ i, if i ∈ S then if X i then 1 else 0 else 0
  have hY : (fun i => bit (Y i)) = maskedMass S (fun i => bit (X i)) := by
    funext i
    by_cases hi : i ∈ S <;> simp [Y, maskedMass, bit, hi]
  have hk : (k : ℝ) = cellMass S (fun i => bit (X i)) := by
    unfold k cellMass
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> cases hX : X i <;> simp [cell, bit, hi]
  have hdiag : (∑ i, cell S i * bit (X i) ^ 2) = cellMass S (fun i => bit (X i)) := by
    apply Finset.sum_congr rfl
    intro i _
    cases hX : X i <;> simp [bit, hX]
  have heq : quadratic (restrictedDual C S) X = MultipartiteDust.charge C Y k := by
    rw [quadratic, restrictedDual_objective, charge_eq_objective, hY, hk, hdiag]
  rw [heq]
  exact hC.2 Y k

/-- Equal dust cells have total mass s and square mass s²/N. -/
theorem uniform_cell_moments {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ) (hpzero : ∀ i ∈ S, p i = 0) :
    maskedMass S (fun i => p i + s * uniformCellWeights S i) = p ∧
    cellMass S (fun i => p i + s * uniformCellWeights S i) = s ∧
    (∑ i, cell S i * (p i + s * uniformCellWeights S i) ^ 2) = s ^ 2 / (S.card : ℝ) := by
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  refine ⟨?_, ?_, ?_⟩
  · funext i
    by_cases hi : i ∈ S <;> simp [maskedMass, uniformCellWeights, hi, hpzero]
  · unfold cellMass
    have ht (i : Fin m) : cell S i * (p i + s * uniformCellWeights S i) =
        s * uniformCellWeights S i := by
      by_cases hi : i ∈ S <;> simp [cell, uniformCellWeights, hi, hpzero]
    simp_rw [ht]
    rw [← Finset.mul_sum, uniformCellWeights_total S hS, mul_one]
  · have ht (i : Fin m) : cell S i * (p i + s * uniformCellWeights S i) ^ 2 =
        if i ∈ S then s ^ 2 / (S.card : ℝ) ^ 2 else 0 := by
      by_cases hi : i ∈ S
      · simp [cell, uniformCellWeights, hi, hpzero, mul_pow, div_eq_mul_inv]
      · simp [cell, hi]
    simp_rw [ht]
    simp only [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
    field_simp

/-- Restricting an optimal dust dual supplies the reverse finite-cell comparison. -/
theorem dust_value_le_selector_value {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ) (hpzero : ∀ i ∈ S, p i = 0)
    (hp : ∀ i, 0 ≤ p i + s * uniformCellWeights S i ∧
      p i + s * uniformCellWeights S i ≤ 1) :
    MultipartiteDust.value p s ≤ Selector.value (fun i => p i + s * uniformCellWeights S i) := by
  obtain ⟨C, hC, heq⟩ := MultipartiteDust.exists_value_eq p s
  have hdual := objective_le_value (fun i => p i + s * uniformCellWeights S i)
    (restrictedDual C S) hp (restrictedDual_feasible C hC S)
  rw [restrictedDual_objective] at hdual
  obtain ⟨hmask, hmass, hsquare⟩ := uniform_cell_moments S hS p s hpzero
  rw [hmask, hmass, hsquare] at hdual
  have hpen : 0 ≤ MultipartiteDust.penalty C := hC.1.1 _
  have hcorrection : 0 ≤ MultipartiteDust.penalty C * (s ^ 2 / (S.card : ℝ)) / 2 := by positivity
  rw [heq]
  linarith

/-- Exact two-sided finite-cell approximation of the bounded homogeneous dust value.
This is the algebraic value theorem; no physical partition representation is assumed. -/
theorem finite_cell_value_error {m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (p : Fin m → ℝ) (s : ℝ) (hpzero : ∀ i ∈ S, p i = 0)
    (hp : ∀ i, 0 ≤ p i + s * uniformCellWeights S i ∧
      p i + s * uniformCellWeights S i ≤ 1) :
    0 ≤ Selector.value (fun i => p i + s * uniformCellWeights S i) - MultipartiteDust.value p s ∧
      Selector.value (fun i => p i + s * uniformCellWeights S i) - MultipartiteDust.value p s ≤
        s ^ 2 / (2 * (S.card : ℝ)) := by
  constructor
  · exact sub_nonneg.mpr (dust_value_le_selector_value S hS p s hpzero hp)
  · linarith [selector_value_le_dust_add_error S hS p s hpzero hp]

end Erdos1017.DustCellRestriction
