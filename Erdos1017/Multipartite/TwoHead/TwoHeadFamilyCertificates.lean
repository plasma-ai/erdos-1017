module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Tensor certificates for the selected two-head branch

The four exact tensor Bernstein certificates for the selected `t = 1`,
`j = 3` branch of the two-head family. The restricted-family optimization
and the other count-index cases are not part of this module.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Erdos1017.TwoHeadFamilyCertificates

/-- The cleared lower gap `12 (1 + x + S) (rationalLower S x - branchValue S x)`. -/
def gapPolynomial (S x : ℝ) : ℝ :=
  12 * (1 + x ^ 2) * (x + S - x ^ 2 / 2) -
    (1 + x + S) * (10 * x + (6 - 4 * x) * S - S ^ 2)

/-- The anchor-square-normalized cost `C/a²` of the `t = 1`, `j = 3` branch. -/
def branchValue (S x : ℝ) : ℝ := (10 * x + (6 - 4 * x) * S - S ^ 2) / 12

/-- The rational relaxation of the normalized one-head lower bound. -/
def rationalLower (S x : ℝ) : ℝ :=
  (1 + x ^ 2) * (x + S - x ^ 2 / 2) / (1 + x + S)

/-- The one-head lower expression `r²(1-r)/a²` when `a = 1/(1+x+S)`. -/
def splitLower (S x : ℝ) : ℝ :=
  (1 + x ^ 2) * (1 - Real.sqrt (1 + x ^ 2) / (1 + x + S))

private theorem tensor_bernstein_lower (n m : ℕ) (c : Fin (n + 1) → Fin (m + 1) → ℝ)
    (b : ℝ) (hc : ∀ i j, b ≤ c i j) (u v : I) :
    b ≤ ∑ i, ∑ j, c i j * bernstein n i u * bernstein m j v := by
  have hsum : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      b * bernstein n i u * bernstein m j v) ≤
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1), c i j * bernstein n i u * bernstein m j v :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc i j) bernstein_nonneg)
        bernstein_nonneg))
  simp only [← Finset.mul_sum, bernstein.probability, mul_one] at hsum
  exact hsum

/-- All 20 exact tensor coefficients on this rectangle are at least `23/54`. -/
theorem gap_lower_left {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) (4 / 3))
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (23 / 54 : ℝ) ≤ gapPolynomial S x := by
  let u : I := ⟨3 * (S - 1), by constructor <;> nlinarith [hS.1, hS.2]⟩
  let v : I := ⟨2 * x, by constructor <;> nlinarith [hx.1, hx.2]⟩
  have hcert := tensor_bernstein_lower 3 4
    (fun i j => ![
      ![2, 11 / 8, 3 / 4, 1 / 2, 5 / 8],
      ![17 / 9, 89 / 72, 71 / 108, 19 / 36, 61 / 72],
      ![46 / 27, 113 / 108, 29 / 54, 119 / 216, 235 / 216],
      ![40 / 27, 91 / 108, 23 / 54, 131 / 216, 299 / 216]] i j) (23 / 54)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num) u v
  convert hcert using 1
  norm_num [gapPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, u, v]
  ring

/-- All 20 exact tensor coefficients on this rectangle are at least `5/8`. -/
theorem gap_lower_right {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) (4 / 3))
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (5 / 8 : ℝ) ≤ gapPolynomial S x := by
  let u : I := ⟨3 * (S - 1), by constructor <;> nlinarith [hS.1, hS.2]⟩
  let v : I := ⟨2 * x - 1, by constructor <;> nlinarith [hx.1, hx.2]⟩
  have hcert := tensor_bernstein_lower 3 4
    (fun i j => ![
      ![5 / 8, 3 / 4, 5 / 4, 17 / 8, 3],
      ![61 / 72, 7 / 6, 209 / 108, 227 / 72, 40 / 9],
      ![235 / 216, 13 / 8, 145 / 54, 461 / 108, 6],
      ![299 / 216, 467 / 216, 191 / 54, 595 / 108, 208 / 27]] i j) (5 / 8)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num) u v
  convert hcert using 1
  norm_num [gapPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, u, v]
  ring

/-- All 20 exact tensor coefficients on this rectangle are at least `17/108`. -/
theorem gap_upper_left {S x : ℝ} (hS : S ∈ Set.Icc (4 / 3 : ℝ) (5 / 3))
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (17 / 108 : ℝ) ≤ gapPolynomial S x := by
  let u : I := ⟨3 * S - 4, by constructor <;> nlinarith [hS.1, hS.2]⟩
  let v : I := ⟨2 * x, by constructor <;> nlinarith [hx.1, hx.2]⟩
  have hcert := tensor_bernstein_lower 3 4
    (fun i j => ![
      ![40 / 27, 91 / 108, 23 / 54, 131 / 216, 299 / 216],
      ![34 / 27, 23 / 36, 17 / 54, 143 / 216, 121 / 72],
      ![1, 91 / 216, 23 / 108, 3 / 4, 439 / 216],
      ![20 / 27, 49 / 216, 17 / 108, 49 / 54, 535 / 216]] i j) (17 / 108)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num) u v
  convert hcert using 1
  norm_num [gapPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, u, v]
  ring

/-- All 20 exact tensor coefficients on this rectangle are at least `299/216`. -/
theorem gap_upper_right {S x : ℝ} (hS : S ∈ Set.Icc (4 / 3 : ℝ) (5 / 3))
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (299 / 216 : ℝ) ≤ gapPolynomial S x := by
  let u : I := ⟨3 * S - 4, by constructor <;> nlinarith [hS.1, hS.2]⟩
  let v : I := ⟨2 * x - 1, by constructor <;> nlinarith [hx.1, hx.2]⟩
  have hcert := tensor_bernstein_lower 3 4
    (fun i j => ![
      ![299 / 216, 467 / 216, 191 / 54, 595 / 108, 208 / 27],
      ![121 / 72, 583 / 216, 79 / 18, 27 / 4, 254 / 27],
      ![439 / 216, 179 / 54, 577 / 108, 1753 / 216, 304 / 27],
      ![535 / 216, 437 / 108, 695 / 108, 2083 / 216, 359 / 27]] i j) (299 / 216)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num) u v
  convert hcert using 1
  norm_num [gapPolynomial, Fin.sum_univ_succ, bernstein_apply, Nat.choose, u, v]
  ring

/-- The four closed rectangles cover the whole selected-branch certificate domain. -/
theorem gapPolynomial_pos {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) (5 / 3))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < gapPolynomial S x := by
  by_cases hS' : S ≤ 4 / 3
  · by_cases hx' : x ≤ 1 / 2
    · exact (by norm_num : (0 : ℝ) < 23 / 54).trans_le
        (gap_lower_left ⟨hS.1, hS'⟩ ⟨hx.1, hx'⟩)
    · exact (by norm_num : (0 : ℝ) < 5 / 8).trans_le
        (gap_lower_right ⟨hS.1, hS'⟩ ⟨le_of_not_ge hx', hx.2⟩)
  · by_cases hx' : x ≤ 1 / 2
    · exact (by norm_num : (0 : ℝ) < 17 / 108).trans_le
        (gap_upper_left ⟨le_of_not_ge hS', hS.2⟩ ⟨hx.1, hx'⟩)
    · exact (by norm_num : (0 : ℝ) < 299 / 216).trans_le
        (gap_upper_right ⟨le_of_not_ge hS', hS.2⟩ ⟨le_of_not_ge hx', hx.2⟩)

/-- Exact clearing of the selected-branch rational gap, with its denominator paid. -/
theorem cleared_gap_identity (S x : ℝ) (hden : 1 + x + S ≠ 0) :
    12 * (1 + x + S) * (rationalLower S x - branchValue S x) = gapPolynomial S x := by
  unfold rationalLower branchValue gapPolynomial
  field_simp

/-- The selected `t = 1`, `j = 3` cost is strictly below the rational lower bound. -/
theorem branchValue_lt_rationalLower {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) (5 / 3))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : branchValue S x < rationalLower S x := by
  have hden : 0 < 1 + x + S := by linarith [hS.1, hx.1]
  have hpos := gapPolynomial_pos hS hx
  rw [← cleared_gap_identity S x hden.ne'] at hpos
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity : 0 < 12 * (1 + x + S))).mp hpos)

theorem sqrt_one_add_sq_le (x : ℝ) : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 / 2 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (x ^ 2)]

/-- The square-root expression is above its rational relaxation on this domain. -/
theorem rationalLower_le_splitLower {S x : ℝ} (hS : 1 ≤ S) (hx : 0 ≤ x) :
    rationalLower S x ≤ splitLower S x := by
  have hden : 0 < 1 + x + S := by linarith
  have hroot := sqrt_one_add_sq_le x
  unfold rationalLower splitLower
  apply (div_le_iff₀ hden).mpr
  field_simp
  nlinarith [mul_nonneg (show 0 ≤ 1 + x ^ 2 by positivity)
    (sub_nonneg.mpr hroot)]

/-- This selected branch is strictly below the explicit normalized split lower expression.
The separate one-head lower-bound theorem licenses its use against the actual split value. -/
theorem branchValue_lt_splitLower {S x : ℝ} (hS : S ∈ Set.Icc (1 : ℝ) (5 / 3))
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : branchValue S x < splitLower S x :=
  (branchValue_lt_rationalLower hS hx).trans_le (rationalLower_le_splitLower hS.1 hx.1)

end Erdos1017.TwoHeadFamilyCertificates
