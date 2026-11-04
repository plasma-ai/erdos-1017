module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.Ring

/-!
# Bernstein to power basis conversion

This module defines the integer power coefficients `powerCoeff` of a finite
Bernstein coefficient array and shows that the power expansion equals the
Bernstein polynomial, so one finite coefficient certificate proves a polynomial
identity at every point of the unit interval (`bernstein_eq_of_coeff_eq`).
-/

@[expose] public section

open Polynomial
open scoped BigOperators unitInterval

namespace Erdos1017.BernsteinPower

/-- The integer power coefficients of a finite Bernstein coefficient array. -/
def powerCoeff (n : ℕ) (c : Fin (n + 1) → ℤ) (k : ℕ) : ℤ :=
  ∑ i, if i.val ≤ k then
    c i * (n.choose i.val : ℤ) * ((n - i.val).choose (k - i.val) : ℤ) *
      (-1) ^ (k - i.val) else 0

private theorem coeff_one_sub_X_pow (n k : ℕ) :
    ((1 - X : ℤ[X]) ^ n).coeff k = (n.choose k : ℤ) * (-1) ^ k := by
  rw [show (1 - X : ℤ[X]) = -X + 1 by ring, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff]
  have hterm (i : ℕ) :
      (((-X : ℤ[X]) ^ i) * (n.choose i : ℤ[X])).coeff k =
        (-1 : ℤ) ^ i * (if i = k then 1 else 0) * (n.choose i : ℤ) := by
    rw [show (-X : ℤ[X]) ^ i = C ((-1 : ℤ) ^ i) * X ^ i by
      rw [neg_pow]
      simp only [map_pow, map_neg, map_one]]
    rw [show (n.choose i : ℤ[X]) = C (n.choose i : ℤ) by simp]
    simp only [coeff_mul_C, coeff_C_mul, coeff_X_pow]
    by_cases h : i = k
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [hterm]
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro j _ hjk
    simp [hjk]
  · intro hk
    have hnk : n < k := by simpa using hk
    simp [Nat.choose_eq_zero_of_lt hnk]

private theorem coeff_bernstein (n i k : ℕ) :
    (bernsteinPolynomial ℤ n i).coeff k =
      if i ≤ k then (n.choose i : ℤ) * ((n - i).choose (k - i) : ℤ) *
        (-1) ^ (k - i) else 0 := by
  rw [bernsteinPolynomial, show (n.choose i : ℤ[X]) = C (n.choose i : ℤ) by simp]
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one_sub_X_pow]
  split_ifs <;> ring

/-- Coefficient extraction performs only finite integer arithmetic. -/
theorem powerCoeff_eq_coeff (n : ℕ) (c : Fin (n + 1) → ℤ) (k : ℕ) :
    powerCoeff n c k = (∑ i, C (c i) * bernsteinPolynomial ℤ n i.val).coeff k := by
  simp only [powerCoeff, finsetSum_coeff, coeff_C_mul, coeff_bernstein]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

private theorem powerCoeff_eq_zero (n : ℕ) (c : Fin (n + 1) → ℤ) {k : ℕ}
    (hk : n < k) : powerCoeff n c k = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val ≤ k := by omega
  have hchoose : n - i.val < k - i.val := by omega
  simp [hi, Nat.choose_eq_zero_of_lt hchoose]

/-- The finite integer power expansion is the original Bernstein polynomial. -/
theorem polynomial_eq (n : ℕ) (c : Fin (n + 1) → ℤ) :
    (∑ i, C (c i) * bernsteinPolynomial ℤ n i.val) =
      ∑ k : Fin (n + 1), C (powerCoeff n c k.val) * X ^ k.val := by
  ext k
  rw [← powerCoeff_eq_coeff, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hk : k < n + 1
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro j _ hj
      have hne : k ≠ j.val := by
        intro he
        apply hj
        exact Fin.ext he.symm
      simp [hne]
    · simp
  · rw [powerCoeff_eq_zero n c (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hne : k ≠ j.val := by omega
    simp [hne]

/-- Transport an integer coefficient calculation to evaluation at any real point. -/
theorem eval_eq_sum_power (n : ℕ) (c : Fin (n + 1) → ℤ) (x : ℝ) :
    (∑ i, (c i : ℝ) * (n.choose i.val : ℝ) * x ^ i.val * (1 - x) ^ (n - i.val)) =
      ∑ k : Fin (n + 1), (powerCoeff n c k.val : ℝ) * x ^ k.val := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) x) (polynomial_eq n c)
  simp only [bernsteinPolynomial, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow,
    eval₂_X, eval₂_sub, eval₂_one, eval₂_natCast] at h
  simpa only [Int.coe_castRingHom, mul_assoc] using h

/-- A single finite coefficient certificate proves the identity for every point
of the unit interval, without simplifying the real Bernstein sum for each row. -/
theorem bernstein_eq_of_coeff_eq (n : ℕ) (c d : Fin (n + 1) → ℤ)
    (h : ∀ k : Fin (n + 1), powerCoeff n c k.val = d k) (x : I) :
    (∑ i, (c i : ℝ) * bernstein n i x) =
      ∑ k : Fin (n + 1), (d k : ℝ) * (x : ℝ) ^ k.val := by
  simpa only [bernstein_apply, ← mul_assoc, h] using eval_eq_sum_power n c (x : ℝ)

end Erdos1017.BernsteinPower
