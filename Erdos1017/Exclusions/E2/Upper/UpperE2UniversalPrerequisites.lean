module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Polynomial prerequisites for the universal upper `E₂` branch

`gammaFloor` is the linear lower bound for the original upper-`E₂` intercept; a
positive coefficient floor gives a positive two-parameter Bernstein polynomial
on the closed unit square, and the concave universal-hole deficit quadratic
`dhQuadratic` stays positive across the physical resource interval.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators unitInterval

namespace Erdos1017.UpperE2UniversalScalar

/-- The linear lower bound for the original upper-E2 intercept. -/
def gammaFloor (ell : ℝ) : ℝ := 16477 / 67100 - 23 * ell / 100

/-- A positive coefficient floor gives a positive two-parameter
Bernstein polynomial on the closed unit square. -/
theorem bernstein_sum₂_pos (n m : ℕ) (eps : ℝ) (heps : 0 < eps)
    (c : Fin (n + 1) → Fin (m + 1) → ℝ)
    (hc : ∀ i j, eps ≤ c i j) (x y : I) :
    0 < ∑ i, ∑ j, c i j * bernstein n i x * bernstein m j y := by
  have hsum : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      eps * bernstein n i x * bernstein m j y) ≤
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
        c i j * bernstein n i x * bernstein m j y := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right (hc i j)
        (mul_nonneg bernstein_nonneg bernstein_nonneg))
  have hbase : (∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
      eps * bernstein n i x * bernstein m j y) = eps := by
    calc
      _ = ∑ i : Fin (n + 1), eps * bernstein n i x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum, bernstein.probability, mul_one]
      _ = eps := by
        rw [← Finset.mul_sum, bernstein.probability, mul_one]
  rw [hbase] at hsum
  exact heps.trans_le hsum

def zeroPricePolynomial (A ell : ℝ) : ℝ :=
  2 * ell ^ 2 * A * gammaFloor ell -
    ((3 - 2 * ell) * A - 6 * gammaFloor ell) *
      (ell + A * (1 + ell - 4 * ell ^ 2) - gammaFloor ell * (1 + 6 * ell))

/-- The exact upper-E2 zero-price polynomial exceeds the required
strict `1/200` margin on the full closed two-parameter box. -/
theorem zero_price_margin {A ell : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11)) :
    (1 / 200 : ℝ) * 2 * ell ^ 2 * A < zeroPricePolynomial A ell := by
  let x : I := ⟨(A - 1 / 3) / (93 / 250 - 1 / 3), by
    constructor <;> norm_num at * <;> linarith [hA.1, hA.2]⟩
  let y : I := ⟨(ell - 4 / 5) / (9 / 11 - 4 / 5), by
    constructor <;> norm_num at * <;> linarith [hell.1, hell.2]⟩
  have hpos := bernstein_sum₂_pos 2 3 (1 / 100000) (by norm_num)
    (fun i j => ![
      ![14381895203 / 2532605625000, 15152933381 / 3343039425000,
        56001706 / 16715197125, 3165589 / 1485795300],
      ![28497508657 / 8442018750000, 8214463531 / 3482332734375,
        7321637669 / 5571732375000, 59520177 / 247632550000],
      ![9368714607 / 3517507812500, 28332883093 / 15477034375000,
        378100826 / 386925859375, 12690123 / 123816275000]] i j)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num) x y
  have heq : zeroPricePolynomial A ell - (1 / 200 : ℝ) * 2 * ell ^ 2 * A =
      ∑ i : Fin 3, ∑ j : Fin 4,
        ![
          ![14381895203 / 2532605625000, 15152933381 / 3343039425000,
            56001706 / 16715197125, 3165589 / 1485795300],
          ![28497508657 / 8442018750000, 8214463531 / 3482332734375,
            7321637669 / 5571732375000, 59520177 / 247632550000],
          ![9368714607 / 3517507812500, 28332883093 / 15477034375000,
            378100826 / 386925859375, 12690123 / 123816275000]] i j *
          bernstein 2 i x * bernstein 3 j y := by
    norm_num [zeroPricePolynomial, gammaFloor, Fin.sum_univ_succ,
      bernstein_apply, Nat.choose, x, y]
    ring
  rw [← heq] at hpos
  linarith

/-- The lower-intercept row resource in the error certificate. -/
def errorRp (A ell : ℝ) : ℝ :=
  ell + gammaFloor ell - (1 + ell) * A

/-- The positive recipient resource in the error certificate. -/
def errorRr (A ell : ℝ) : ℝ :=
  (2 * ell - 1) * A + 3 * gammaFloor ell

/-- The residual degree allowance in the error certificate. -/
def errorDd (A ell : ℝ) : ℝ :=
  2 * ell * (1 - 2 * A) - errorRp A ell

def errorPolynomial (A ell : ℝ) : ℝ :=
  12 / 5 * gammaFloor ell * errorRp A ell * errorRr A ell -
    (A - 3 * gammaFloor ell) * errorDd A ell ^ 2

/-- The exact upper-E2 error polynomial is positive on the full
closed two-parameter box. -/
theorem error_polynomial_pos {A ell : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11)) :
    0 < errorPolynomial A ell := by
  let x : I := ⟨(A - 1 / 3) / (93 / 250 - 1 / 3), by
    constructor <;> norm_num at * <;> linarith [hA.1, hA.2]⟩
  let y : I := ⟨(ell - 4 / 5) / (9 / 11 - 4 / 5), by
    constructor <;> norm_num at * <;> linarith [hell.1, hell.2]⟩
  have hpos := bernstein_sum₂_pos 3 3 (1 / 100000) (by norm_num)
    (fun i j => ![
      ![19806692419472929 / 5098135123125000000,
        13344526293331 / 4078508098500000, 7970787171 / 3021117110000,
        11771209 / 5932375416],
      ![85940506787112487 / 25490675615625000000,
        604157874805537 / 212422296796875000,
        193706019601 / 84266696250000, 5316671 / 3064243500],
      ![127977076794373579 / 42484459359375000000,
        1213079340660339 / 472049548437500000,
        3986524085839 / 1888198193750000, 50567640793 / 30897788625000],
      ![12718952699671233 / 4720495484375000000,
        550573615780039 / 236024774218750000,
        92369794810723 / 47204954843750000,
        84032763306 / 53641994140625]] i j)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num) x y
  have heq : errorPolynomial A ell =
      ∑ i : Fin 4, ∑ j : Fin 4,
        ![
          ![19806692419472929 / 5098135123125000000,
            13344526293331 / 4078508098500000, 7970787171 / 3021117110000,
            11771209 / 5932375416],
          ![85940506787112487 / 25490675615625000000,
            604157874805537 / 212422296796875000,
            193706019601 / 84266696250000, 5316671 / 3064243500],
          ![127977076794373579 / 42484459359375000000,
            1213079340660339 / 472049548437500000,
            3986524085839 / 1888198193750000, 50567640793 / 30897788625000],
          ![12718952699671233 / 4720495484375000000,
            550573615780039 / 236024774218750000,
            92369794810723 / 47204954843750000,
            84032763306 / 53641994140625]] i j *
          bernstein 3 i x * bernstein 3 j y := by
    norm_num [errorPolynomial, errorRp, errorRr, errorDd, gammaFloor,
      Fin.sum_univ_succ, bernstein_apply, Nat.choose, x, y]
    ring
  rw [heq]
  exact hpos

/-- The lower resource endpoint for the universal-hole deficit quadratic. -/
def dhRp (A ell : ℝ) : ℝ := ell + 7 / 122 - (1 + ell) * A

/-- Constant coefficient of the cleared universal-hole deficit quadratic. -/
def dhG0 (A ell : ℝ) : ℝ :=
  (3 * (7 / 122) - A * (1 - ell)) *
      (18 * A - 22 * A ^ 2 - 3 - 3509 / 14884) -
    2 * A * (2 - 4 * A) * (1 - ell - 2 * (7 / 122))

/-- Linear coefficient of the cleared universal-hole deficit quadratic. -/
def dhG1 (A ell : ℝ) : ℝ :=
  (3 * (7 / 122) - A * (1 - ell)) * (2 - 8 * A) +
    2 * A * ((2 - 4 * A) * (1 - ell) + (1 - ell - 2 * (7 / 122)))

/-- Negative quadratic coefficient of the cleared universal-hole deficit. -/
def dhG2 (A ell : ℝ) : ℝ := -2 * A * (1 - ell)

/-- The cleared deficit expression before the concavity endpoint step. -/
def dhQuadratic (A ell u : ℝ) : ℝ :=
  dhG0 A ell + dhG1 A ell * u + dhG2 A ell * u ^ 2

private def dhLowCoeff : Fin 4 → Fin 4 → ℝ :=
  fun i j => ![
    ![17731211 / 1532121750, 87704237 / 5056001775,
      51843773 / 2224640781, 480458791 / 16314032394],
    ![7271087183 / 383030437500, 15799689674 / 632000221875,
      11568370417 / 370773463500, 38328441218 / 1019627024625],
    ![98069828581 / 3989900390625, 323920639733 / 10533337031250,
      4299340593529 / 115866707343750, 3708493321333 / 84968918718750],
    ![1603642481079 / 55415283203125, 389813981049 / 11083056640625,
      8921624544609 / 214567976562500, 28419909166794 / 590061935546875]] i j

private def dhHighCoeff : Fin 4 → Fin 2 → ℝ :=
  fun i j => ![
    ![1510591 / 245139480, 5094911 / 539306856],
    ![7806919 / 1021414500, 68071039 / 6128487000],
    ![11209439261 / 1276768125000, 34792216163 / 2808889875000],
    ![43148278947 / 4433222656250, 524004268701 / 39012359375000]] i j

private theorem dh_low_endpoint_pos {A ell : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11)) :
    0 < 4 * ell ^ 2 * dhG0 A ell +
      2 * ell * dhRp A ell * dhG1 A ell + dhRp A ell ^ 2 * dhG2 A ell := by
  let x : I := ⟨(A - 1 / 3) / (93 / 250 - 1 / 3), by
    constructor <;> norm_num at * <;> linarith [hA.1, hA.2]⟩
  let y : I := ⟨(ell - 4 / 5) / (9 / 11 - 4 / 5), by
    constructor <;> norm_num at * <;> linarith [hell.1, hell.2]⟩
  have hpos := bernstein_sum₂_pos 3 3 (1 / 100000) (by norm_num) dhLowCoeff
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [dhLowCoeff]) x y
  have heq : 4 * ell ^ 2 * dhG0 A ell +
      2 * ell * dhRp A ell * dhG1 A ell + dhRp A ell ^ 2 * dhG2 A ell =
      ∑ i : Fin 4, ∑ j : Fin 4,
        dhLowCoeff i j * bernstein 3 i x * bernstein 3 j y := by
    norm_num [dhLowCoeff, dhG0, dhG1, dhG2, dhRp,
      Fin.sum_univ_succ, bernstein_apply, Nat.choose, x, y]
    ring
  rw [heq]
  exact hpos

private theorem dh_high_endpoint_pos {A ell : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11)) :
    0 < dhQuadratic A ell (1 - 2 * A) := by
  let x : I := ⟨(A - 1 / 3) / (93 / 250 - 1 / 3), by
    constructor <;> norm_num at * <;> linarith [hA.1, hA.2]⟩
  let y : I := ⟨(ell - 4 / 5) / (9 / 11 - 4 / 5), by
    constructor <;> norm_num at * <;> linarith [hell.1, hell.2]⟩
  have hpos := bernstein_sum₂_pos 3 1 (1 / 100000) (by norm_num) dhHighCoeff
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [dhHighCoeff]) x y
  have heq : dhQuadratic A ell (1 - 2 * A) =
      ∑ i : Fin 4, ∑ j : Fin 2,
        dhHighCoeff i j * bernstein 3 i x * bernstein 1 j y := by
    norm_num [dhHighCoeff, dhQuadratic, dhG0, dhG1, dhG2,
      Fin.sum_univ_succ, bernstein_apply, Nat.choose, x, y]
    ring
  rw [heq]
  exact hpos

/-- The exact concave deficit quadratic stays positive across the entire
physical resource interval. Its two endpoint signs are Lean-checked
Bernstein identities, including both closed parameter-box boundaries. -/
theorem dh_quadratic_pos {A ell u : ℝ}
    (hA : A ∈ Icc (1 / 3 : ℝ) (93 / 250))
    (hell : ell ∈ Icc (4 / 5 : ℝ) (9 / 11))
    (hu : dhRp A ell / (2 * ell) ≤ u ∧ u ≤ 1 - 2 * A) :
    0 < dhQuadratic A ell u := by
  let lo := dhRp A ell / (2 * ell)
  let hi := 1 - 2 * A
  have hellpos : 0 < ell := by linarith [hell.1]
  have hlowpoly := dh_low_endpoint_pos hA hell
  have hloweq : 4 * ell ^ 2 * dhQuadratic A ell lo =
      4 * ell ^ 2 * dhG0 A ell +
        2 * ell * dhRp A ell * dhG1 A ell +
          dhRp A ell ^ 2 * dhG2 A ell := by
    dsimp [lo, dhQuadratic]
    field_simp [hellpos.ne']
    ring
  have hlow : 0 < dhQuadratic A ell lo := by
    have hmul : 0 < 4 * ell ^ 2 * dhQuadratic A ell lo := by
      rw [hloweq]
      exact hlowpoly
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4 * ell ^ 2)).mp hmul
  have hhigh : 0 < dhQuadratic A ell hi := dh_high_endpoint_pos hA hell
  have hg2 : dhG2 A ell ≤ 0 := by
    unfold dhG2
    have hprod : 0 ≤ 2 * A * (1 - ell) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [hA.1]))
        (by linarith [hell.2])
    nlinarith
  by_cases heq : lo = hi
  · have hueq : u = lo := le_antisymm (heq ▸ hu.2) hu.1
    simpa only [hueq] using hlow
  · have hgap : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne
      (hu.1.trans hu.2) heq)
    have hleft : 0 ≤ u - lo := sub_nonneg.mpr hu.1
    have hright : 0 ≤ hi - u := sub_nonneg.mpr hu.2
    have hchord : (hi - lo) * dhQuadratic A ell u =
        (hi - u) * dhQuadratic A ell lo +
          (u - lo) * dhQuadratic A ell hi -
            dhG2 A ell * (u - lo) * (hi - u) * (hi - lo) := by
      unfold dhQuadratic
      ring
    have hpositive : 0 < (hi - lo) * dhQuadratic A ell u := by
      rw [hchord]
      have hterm : 0 ≤ -(dhG2 A ell) * (u - lo) * (hi - u) * (hi - lo) := by
        exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr hg2) hleft)
          hright) hgap.le
      by_cases heqlo : u = lo
      · subst u
        simpa only [sub_self, mul_zero, zero_mul, sub_zero, add_zero] using
          mul_pos hgap hlow
      · have hstrict : 0 < u - lo := sub_pos.mpr (lt_of_le_of_ne hu.1 (Ne.symm heqlo))
        have hfirst : 0 ≤ (hi - u) * dhQuadratic A ell lo :=
          mul_nonneg hright hlow.le
        have hsecond : 0 < (u - lo) * dhQuadratic A ell hi :=
          mul_pos hstrict hhigh
        linarith
    exact (mul_pos_iff_of_pos_left hgap).mp hpositive

end Erdos1017.UpperE2UniversalScalar
