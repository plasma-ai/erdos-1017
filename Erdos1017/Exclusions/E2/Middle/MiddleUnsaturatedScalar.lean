module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Mathlib.Tactic.Linarith

/-!
# Scalar facts for the middle unsaturated count

The order-two numerator `P(q) = 4-16q-39q^2+56q^3-5q^4` and floor stay positive
through `187/1000`, the middle selector value `D_ell(A)` stays below the gap
floor for every peak mass in `[1/4, 3/10]`, and the sharp count cell with the
endpoint budget caps the selector value once `ell ≥ 2/3`.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleUnsaturatedScalar

open LowerE2Scalar

/-- The order-two numerator `P(q) = 4-16q-39q^2+56q^3-5q^4` stays positive
through `187/1000`. The exact remainder at the closed endpoint is
`858042639/200000000000`, and the quotient is positive on the interval. -/
theorem pairNumerator_pos {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (187 / 1000)) :
    0 < pairNumerator q := by
  have hq2 : q ^ 2 ≤ (187 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hq.1 hq.2 2
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq.1 3
  have hquot : 0 ≤ 21367432015 / 1000000000 + 28702845 / 1000000 * q -
      55065 / 1000 * q ^ 2 + 5 * q ^ 3 := by
    norm_num at hq2
    linarith [hq.1]
  have hprod := mul_nonneg (sub_nonneg.mpr hq.2) hquot
  have hid : pairNumerator q = 858042639 / 200000000000 + (187 / 1000 - q) *
      (21367432015 / 1000000000 + 28702845 / 1000000 * q -
        55065 / 1000 * q ^ 2 + 5 * q ^ 3) := by
    unfold pairNumerator
    ring
  rw [hid]
  linarith

/-- The order-two floor is positive through `187/1000`. -/
theorem pairFloor_pos {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (187 / 1000)) : 0 < pairFloor q := by
  have hR := denominator_pos hq.1
  unfold pairFloor
  exact div_pos (pairNumerator_pos hq) (by positivity)

/-- On the remaining no-saturation range, the middle selector value
`D_ell(A) = (-1+8A-(7+6 ell)A^2)/6` stays below the gap floor for every
peak mass in `[1/4, 3/10]`. Both endpoints of the `q` interval are closed. -/
theorem selectorValue_lt_gapFloor {q A : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hA : A ∈ Icc (1 / 4 : ℝ) (3 / 10)) :
    (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 < gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hden : 0 < 2 + q := by linarith
  have hell : 9 / 11 ≤ multiplier q ∧ multiplier q ≤ 1 := by
    unfold multiplier
    constructor
    · rw [le_div_iff₀ hden]
      linarith [hq.2]
    · rw [div_le_iff₀ hden]
      linarith
  have hbracket : 0 ≤ 8 - (7 + 6 * multiplier q) * (3 / 10 + A) := by
    have hsum : 3 / 10 + A ≤ (3 / 5 : ℝ) := by linarith [hA.2]
    have hcoef : 7 + 6 * multiplier q ≤ 13 := by linarith [hell.2]
    nlinarith [mul_le_mul hcoef hsum (by linarith [hA.1]) (by norm_num : (0 : ℝ) ≤ 13)]
  have hmono := mul_nonneg (sub_nonneg.mpr hA.2) hbracket
  have hvertex : (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 ≤ 361 / 6600 := by
    nlinarith [hmono, hell.1]
  have hfloor : 361 / 6600 < gapFloor q := by
    have hR := denominator_pos hq0
    have hq2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
    unfold gapFloor
    rw [lt_div_iff₀ (by positivity)]
    unfold denominator
    norm_num at hq2
    nlinarith [hq.1]
  linarith

/-- The sharp middle count cell and the actual endpoint budget give the
selector value cap once `ell >= 2/3`; only the nonnegative endpoint energy
and residual square mass are discarded. -/
theorem selectorValue_of_sharp_budget {A ell σ C γ E : ℝ}
    (hA : 0 < A) (hell : 2 / 3 ≤ ell) (hσ : 0 ≤ σ) (hE : 0 ≤ E)
    (hC : C ≤ A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12 + σ / 3)
    (hbudget : γ + E = 2 * C - ell * (A ^ 2 + σ)) :
    γ ≤ (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hid : 2 * (A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12) -
      ell * A ^ 2 = (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 := by
    field_simp
    ring
  have hσterm : (2 / 3 - ell) * σ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hσ
  nlinarith [hid, hC, hbudget, hE, hσterm]

end Erdos1017.MiddleUnsaturatedScalar
