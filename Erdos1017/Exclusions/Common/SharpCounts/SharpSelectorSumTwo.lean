module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorSliceMaxima
public import Erdos1017.Multipartite.Selector.SelectorOptimalValue

/-!
# Sharp selector bound at total load two

The unrestricted Boolean dual obeys the sharp sum-two square correction, with
the centered conditions derived from a compact-slice maximum, and finite
primal-dual attainment turns this into the sharp selector value bound at total
load two (`value_le_sumTwo`).
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators Classical

namespace Erdos1017.Selector.Sharp

variable {n : ℕ}

/-- The Hessian of the actual selector objective minus one third of its square mass. -/
def excessHessian (D : Dual n) (i j : Fin n) : ℝ := D.beta i j - if i = j then 2 / 3 else 0

private theorem excessHessian_symm (D : Dual n) (i j : Fin n) :
    excessHessian D i j = excessHessian D j i := by
  unfold excessHessian
  rw [D.beta_symm i j]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [hij, Ne.symm hij]

private theorem excessHessian_diag (D : Dual n) (i : Fin n) :
    excessHessian D i i = -(2 / 3 : ℝ) := by simp [excessHessian, D.beta_diag]

private theorem excess_polynomial (D : Dual n) (p : Fin n → ℝ) :
    quadraticPolynomial D.alpha (excessHessian D) p = objective p D - (∑ i, (p i) ^ 2) / 3 := by
  have hrow (i : Fin n) : matrixRow (excessHessian D) p i =
      (∑ j, D.beta i j * p j) - (2 / 3) * p i := by
    simp [matrixRow, excessHessian, sub_mul, ite_mul, Finset.sum_sub_distrib]
  unfold quadraticPolynomial matrixQuadratic
  simp_rw [hrow, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  unfold objective
  have hpair : (∑ i, ∑ j, p i * (D.beta i j * p j)) =
      ∑ i, ∑ j, D.beta i j * (p i * p j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsq : (∑ i, p i * (2 / 3 * p i)) = (2 / 3) * ∑ i, (p i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpair, hsq]
  ring

private theorem triple_test (D : Dual n) (hD : DualFeasible D)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    D.alpha i + D.alpha j + D.alpha k + D.beta i j + D.beta i k + D.beta j k ≤ 1 := by
  let X : Selection n := fun l => decide (l = i ∨ l = j ∨ l = k)
  have hb (l : Fin n) : bit (X l) =
      (if l = i then 1 else 0) + (if l = j then 1 else 0) + (if l = k then 1 else 0) := by
    by_cases hi : l = i
    · subst l
      simp [X, bit, hij, hik]
    by_cases hj : l = j
    · subst l
      simp [X, bit, Ne.symm hij, hjk]
    by_cases hk : l = k
    · subst l
      simp [X, bit, Ne.symm hik, Ne.symm hjk]
    simp [X, bit, hi, hj, hk]
  have ht := hD X
  unfold quadratic objective at ht
  simp only [hb, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, D.beta_diag] at ht
  rw [D.beta_symm j i, D.beta_symm k i, D.beta_symm k j] at ht
  linarith

/-- The unrestricted Boolean dual obeys the sharp sum-two square correction.
The centered conditions are derived from an actual compact-slice maximum. -/
theorem objective_le_sumTwo (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hs : ∑ i, p i = 2) (D : Dual n) (hD : DualFeasible D) :
    objective p D ≤ (2 + ∑ i, (p i) ^ 2) / 3 := by
  by_contra h
  have hbad : 2 / 3 < quadraticPolynomial D.alpha (excessHessian D) p := by
    rw [excess_polynomial]
    linarith
  obtain ⟨x, hx, hmax⟩ := exists_sumTwoSlice_max D.alpha (excessHessian D) p ⟨hp, hs⟩
  have hxbox : ∀ i, x i ∈ Icc (0 : ℝ) 1 := hx.1
  have hxsum : ∑ i, x i = 2 := hx.2
  have hexcess : 2 / 3 < quadraticPolynomial D.alpha (excessHessian D) x :=
    hbad.trans_le (hmax ⟨hp, hs⟩)
  have hxinterior (i : Fin n) : x i ∈ Ico (0 : ℝ) 1 := by
    refine ⟨(hxbox i).1, ?_⟩
    by_contra hi
    have hxi : x i = 1 := le_antisymm (hxbox i).2 (le_of_not_gt hi)
    have hsq : 1 ≤ ∑ k, (x k) ^ 2 := by
      simpa only [hxi, one_pow] using
        (Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i))
    have hb := Selector.objective_le_one x D hxbox hD
    rw [excess_polynomial] at hexcess
    linarith
  let C := excessHessian D
  let K := centeredMatrix C x
  let lam : ℝ := (∑ i, x i * (D.alpha i + matrixRow C x i)) / 2
  let L : ℝ := lam + 2 / 3 - matrixQuadratic C x / 4
  have hvariation (i : Fin n) (hi : 0 < x i) :
      D.alpha i + matrixRow C x i = lam ∧ 0 ≤ K i i := by
    have hsupport (k : Fin n) (hk : x k = 0) : centeredDirection x i k = 0 := by
      have hki : k ≠ i := by intro he; subst k; linarith
      simp [centeredDirection, hki, hk]
    obtain ⟨hfirst, hsecond⟩ := variations_of_sumTwoSlice_max D.alpha C
      (excessHessian_symm D) x hxinterior hxsum hmax (centeredDirection x i)
      (centeredDirection_sum x hxsum i) hsupport
    have hfirst' : D.alpha i + matrixRow C x i - lam = 0 := by
      dsimp only [lam]
      simpa only [centeredDirection, sub_mul, ite_mul, one_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        div_mul_eq_mul_div, ← Finset.sum_div] using hfirst
    refine ⟨by linarith, ?_⟩
    dsimp only [K]
    rw [centeredMatrix_diagonal C (excessHessian_symm D)]
    linarith
  have halpha (i : Fin n) (hi : 0 < x i) : D.alpha i = L - 2 * K i i := by
    have hg := (hvariation i hi).1
    dsimp [K, L, centeredMatrix]
    have hdiag : C i i = -(2 / 3 : ℝ) := excessHessian_diag D i
    rw [hdiag]
    linarith
  have hbeta (i j : Fin n) (hij : i ≠ j) :
      D.beta i j = K i i + K j j - 2 * K i j - 2 / 3 := by
    have hdistance := centeredMatrix_distance C (excessHessian_diag D) x i j
    simpa only [C, K, excessHessian, hij, ite_false, sub_zero] using hdistance
  have htests (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hi : 0 < x i) (hj : 0 < x j) (hk : 0 < x k) :
      3 * L - 3 - 2 * (K i j + K i k + K j k) ≤ 0 := by
    have ht := triple_test D hD i j k hij hik hjk
    rw [halpha i hi, halpha j hj, halpha k hk, hbeta i j hij, hbeta i k hik, hbeta j k hjk] at ht
    linarith
  have hL : L ≤ 1 := centered_intercept_le_one x hxbox hxsum K
    (centeredMatrix_symm C (excessHessian_symm D) x)
    (centeredMatrix_rows C x hxsum) (fun i hi => (hvariation i hi).2) L htests
    (exists_positive_triple x hxinterior hxsum)
  have hidentity : quadraticPolynomial D.alpha C x = 2 * L - 4 / 3 := by
    dsimp [quadraticPolynomial, L, lam, matrixQuadratic]
    simp only [mul_add, Finset.sum_add_distrib]
    have hlinear : (∑ i, D.alpha i * x i) = ∑ i, x i * D.alpha i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hlinear]
    ring
  rw [hidentity] at hexcess
  linarith

/-- Finite primal-dual attainment turns the unrestricted dual estimate
into the sharp exact selector value bound at total load two. -/
theorem value_le_sumTwo (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hs : ∑ i, p i = 2) : value p ≤ (2 + ∑ i, (p i) ^ 2) / 3 := by
  obtain ⟨_, _, _, D, hD, hvalue, _, _⟩ := value_attained p hp
  rw [← hvalue]
  exact objective_le_sumTwo p hp hs D hD.1

end Erdos1017.Selector.Sharp
