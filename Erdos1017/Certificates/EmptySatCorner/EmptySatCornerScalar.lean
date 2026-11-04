module

public import Erdos1017.Certificates.EmptySatCorner.EmptySatCornerCertificates
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Scalar price bounds for the empty-source saturated corner

The corner certificates yield the contact margin, a contradiction in the
unsaturated case, the signed two-head support price `supportPolynomial`, the
bad-row mass cap, the initial guards of the corner bad region, and positivity of
the price in the exceptional, small-excess, small-`E` and middle-deficit
domains.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.EmptySatCorner

open Set
open scoped BigOperators unitInterval

/-- The actual correlated corner intercept pays the unsaturated triangle
margin throughout the original one-sided slope bracket. -/
theorem contact_margin {A ell gamma : ℝ}
    (hell : ell ∈ Set.Icc (363 / 589 : ℝ) (9 / 11)) (hA : 1 / 3 < A)
    (hfloor : 2 * (138261458236451 / 1116960975000000 : ℝ) -
      ell * (23243417 / 10 ^ 8) < gamma) :
    (1 - ell) * (1 - A) < 3 * gamma := by
  have hdelta : 0 < 1 - ell := by linarith only [hell.2]
  have hline : 2 * (1 - ell) / 3 < 3 * gamma := by
    linarith only [hfloor, hell.2]
  have hp := mul_pos hdelta (show 0 < A - 1 / 3 by linarith only [hA])
  nlinarith only [hp, hline]

/-- The universal trace and the actual unsaturated half-quota conflict
with the corner cost and missing-density enclosure. -/
theorem unsaturated_false {A h c gamma : ℝ}
    (hA : 0 ≤ A) (hgamma : 0 ≤ gamma) (hc : 3 / 25 < c) (hh : h < 6 / 25)
    (htrace : 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * h)
    (hquota : c ≤ A * (1 - A) / 2) : False := by
  have hAlt : A < 2 / 5 := by
    by_contra hn
    have hge : 2 / 5 ≤ A := le_of_not_gt hn
    have hsquare : (2 / 5 : ℝ) ^ 2 ≤ A ^ 2 := by nlinarith only [hge]
    have hp := mul_nonneg hA hgamma
    nlinarith only [htrace, hh, hsquare, hp, sq_nonneg gamma]
  have hp := mul_pos (show 0 < 2 / 5 - A by linarith only [hAlt])
    (show 0 < 3 / 5 - A by linarith only [hAlt])
  nlinarith only [hp, hquota, hc]

/-- The actual signed two-head support price, with its original
correlated excess and truncated support square. -/
def supportPolynomial (delta h X V T : ℝ) : ℝ :=
  delta * (X - 2 * h) - 2 * (1 - delta) * V ^ 2 + (2 * X - 1) * T -
    (1 - X) ^ 2 / 12 + (12 / 25) *
      max ((2 - delta) * V - T - (1 - X) / 12) 0 ^ 2

private def squarePolynomial (delta h X V T : ℝ) : ℝ :=
  delta * (X - 2 * h) - 2 * (1 - delta) * V ^ 2 + (2 * X - 1) * T -
    (1 - X) ^ 2 / 12 + (12 / 25) *
      ((2 - delta) * V - T - (1 - X) / 12) ^ 2

private def referencePolynomial (delta h w : ℝ) : ℝ :=
  squarePolynomial delta h w (3 / 4 - w) 0

private def referenceNumerator (delta h : ℝ) : ℝ :=
  let wn := 2 * h * delta + 37 / 1250
  let vn := 3 * delta / 4 - wn
  let rn := delta - wn
  (37 / 1250) * delta ^ 2 - 2 * (1 - delta) * vn ^ 2 - rn ^ 2 / 12 +
    (12 / 25) * ((2 - delta) * vn - rn / 12) ^ 2

private theorem reference_numerator_chart (x y : I) :
    0 < referenceNumerator (2 / 11 + (2 / 5 - 2 / 11) * (x : ℝ))
      (23 / 100 + (467 / 2000 - 23 / 100) * (y : ℝ)) := by
  let coeff : Fin 5 → Fin 3 → ℝ := fun i j =>
    ![![9865679100, 10349839350, 10821259600],
      ![9439253340, 10283829765, 11108867440],
      ![5742408804, 7085428944, 8400582784],
      ![1772907972, 3677852475, 5546926528],
      ![3144359724, 5537021226, 7889507824]] i j
  have hunit : (∑ i : Fin 5, ∑ j : Fin 3,
      bernstein 4 i x * bernstein 2 j y) = 1 := by
    simp_rw [← Finset.mul_sum, bernstein.probability, mul_one]
    exact bernstein.probability _ _
  have hsum : 1 ≤ ∑ i : Fin 5, ∑ j : Fin 3,
      coeff i j * (bernstein 4 i x * bernstein 2 j y) := by
    rw [← hunit]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hc : 1 ≤ coeff i j := by
      fin_cases i <;> fin_cases j <;> norm_num [coeff]
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hc
      (mul_nonneg bernstein_nonneg bernstein_nonneg))
  have hid : (28595703125000 : ℝ) *
      referenceNumerator (2 / 11 + (2 / 5 - 2 / 11) * (x : ℝ))
        (23 / 100 + (467 / 2000 - 23 / 100) * (y : ℝ)) =
      ∑ i : Fin 5, ∑ j : Fin 3, coeff i j * (bernstein 4 i x * bernstein 2 j y) := by
    norm_num [referenceNumerator, coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  have hpos : 0 < (28595703125000 : ℝ) *
      referenceNumerator (2 / 11 + (2 / 5 - 2 / 11) * (x : ℝ))
        (23 / 100 + (467 / 2000 - 23 / 100) * (y : ℝ)) := by
    rw [hid]
    linarith only [hsum]
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

private theorem reference_polynomial_pos {delta h : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (2 / 5))
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000)) :
    0 < referencePolynomial delta h (2 * h + 37 / (1250 * delta)) := by
  let x : I := ⟨(delta - 2 / 11) / (2 / 5 - 2 / 11), by
    constructor <;> norm_num <;> linarith only [hdelta.1, hdelta.2]⟩
  let y : I := ⟨(h - 23 / 100) / (467 / 2000 - 23 / 100), by
    constructor <;> norm_num <;> linarith only [hh.1, hh.2]⟩
  have hpos := reference_numerator_chart x y
  have hx : 2 / 11 + (2 / 5 - 2 / 11) * (x : ℝ) = delta := by dsimp [x]; ring
  have hy : 23 / 100 + (467 / 2000 - 23 / 100) * (y : ℝ) = h := by dsimp [y]; ring
  rw [hx, hy] at hpos
  have hdelta0 : 0 < delta := by linarith only [hdelta.1]
  have hid : referenceNumerator delta h = delta ^ 2 *
      referencePolynomial delta h (2 * h + 37 / (1250 * delta)) := by
    unfold referenceNumerator referencePolynomial squarePolynomial
    field_simp [hdelta0.ne']
    ring
  rw [hid] at hpos
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hdelta0)).mp hpos

private theorem squarePolynomial_antitone {delta h X T V W : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (2 / 5))
    (hX : X < 137 / 200) (hT : 0 ≤ T)
    (hV : 0 ≤ V) (hVW : V ≤ W) (hW : W ≤ 1 / 4) :
    squarePolynomial delta h X W T ≤ squarePolynomial delta h X V T := by
  have hcoef : -(18 / 625 : ℝ) ≤
      2 * (1 - delta) - (12 / 25) * (2 - delta) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hdelta.2)
      (show 0 ≤ (12 / 25) * delta + 34 / 125 by linarith only [hdelta.1])
    nlinarith only [hp]
  have hsum : 0 ≤ W + V := by linarith only [hV, hVW]
  have hsumhi : W + V ≤ 1 / 2 := by linarith only [hVW, hW]
  have hfactor : 0 ≤
      (2 * (1 - delta) - (12 / 25) * (2 - delta) ^ 2) * (W + V) +
        (24 / 25) * (2 - delta) * (T + (1 - X) / 12) := by
    have hp := mul_nonneg (sub_nonneg.mpr hcoef) hsum
    have hq := mul_nonneg (show 0 ≤ 2 - delta by linarith only [hdelta.2]) hT
    have hr : (8 / 5 : ℝ) * (63 / 200) ≤ (2 - delta) * (1 - X) := by
      have ha : (8 / 5 : ℝ) ≤ 2 - delta := by linarith only [hdelta.2]
      have hb : (63 / 200 : ℝ) ≤ 1 - X := by linarith only [hX]
      exact mul_le_mul ha hb (by norm_num) (by linarith only [hdelta.2])
    nlinarith only [hp, hq, hr, hsumhi]
  have hp := mul_nonneg (sub_nonneg.mpr hVW) hfactor
  have hid : squarePolynomial delta h X V T - squarePolynomial delta h X W T =
      (W - V) * ((2 * (1 - delta) - (12 / 25) * (2 - delta) ^ 2) * (W + V) +
        (24 / 25) * (2 - delta) * (T + (1 - X) / 12)) := by
    unfold squarePolynomial
    ring
  linarith only [hp, hid]

private theorem supportPolynomial_ge_endpoint {delta h X V T : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (2 / 5))
    (hXlo : 1 / 2 < X) (hXhi : X < 137 / 200) (hT : 0 ≤ T)
    (hV : 0 ≤ V) (hVhi : V ≤ 3 / 4 - X)
    (hactive : 0 < (2 - delta) * (3 / 4 - X) - T - (1 - X) / 12) :
    squarePolynomial delta h X (3 / 4 - X) T ≤ supportPolynomial delta h X V T := by
  by_cases hsmall : 0 ≤ (2 - delta) * V - T - (1 - X) / 12
  · have hpoly := squarePolynomial_antitone (h := h) hdelta hXhi hT hV hVhi
      (show 3 / 4 - X ≤ 1 / 4 by linarith only [hXlo])
    simpa only [supportPolynomial, squarePolynomial, max_eq_left hsmall] using hpoly
  · let V0 := (T + (1 - X) / 12) / (2 - delta)
    have hm : 0 < 2 - delta := by linarith only [hdelta.2]
    have hV0 : 0 ≤ V0 := div_nonneg (by linarith only [hT, hXhi]) hm.le
    have hVV0 : V ≤ V0 := (le_div_iff₀ hm).mpr (by linarith only [hsmall])
    have hV0hi : V0 ≤ 3 / 4 - X := (div_le_iff₀ hm).mpr (by linarith only [hactive])
    have hroot : (2 - delta) * V0 - T - (1 - X) / 12 = 0 := by
      dsimp only [V0]
      field_simp [hm.ne']
      ring
    have hpoly := squarePolynomial_antitone (h := h) hdelta hXhi hT hV0 hV0hi
      (show 3 / 4 - X ≤ 1 / 4 by linarith only [hXlo])
    have hsquare : V ^ 2 ≤ V0 ^ 2 := pow_le_pow_left₀ hV hVV0 2
    have hp := mul_nonneg (show 0 ≤ 2 * (1 - delta) by linarith only [hdelta.2])
      (sub_nonneg.mpr hsquare)
    unfold squarePolynomial at hpoly
    rw [hroot] at hpoly
    unfold supportPolynomial
    unfold squarePolynomial
    rw [max_eq_right (le_of_not_ge hsmall)]
    nlinarith only [hpoly, hp]

/-- The original corner support price is strictly positive whenever the
correlated excess is nonpositive. All fifteen rational tensor coefficients
and both monotonicity comparisons are proved on the closed corner box. -/
theorem supportPolynomial_pos_of_nonpositive_excess {delta h X V w : ℝ}
    (hdelta : delta ∈ Icc (2 / 11 : ℝ) (2 / 5))
    (hh : h ∈ Icc (23 / 100 : ℝ) (467 / 2000))
    (hw : 2 * h + 37 / (1250 * delta) < w) (hwX : w ≤ X)
    (hX : X < 137 / 200) (hV : 0 ≤ V) (hVhi : V ≤ 3 / 4 - X) :
    0 < supportPolynomial delta h X V (delta * (X - w)) := by
  have hdelta0 : 0 < delta := by linarith only [hdelta.1]
  let w0 := 2 * h + 37 / (1250 * delta)
  have hdelta_w0 : delta * w0 = 2 * h * delta + 37 / 1250 := by
    dsimp only [w0]
    field_simp
  have hw0lo : 1 / 2 < w0 := by
    have hp := mul_le_mul_of_nonneg_right hh.1 hdelta0.le
    have hmul : delta / 2 < delta * w0 := by
      nlinarith only [hdelta_w0, hp, hdelta.2]
    nlinarith only [hmul, hdelta0]
  have hw0 : w0 < w := hw
  have hwlo : 1 / 2 < w := hw0lo.trans hw0
  have hXlo : 1 / 2 < X := hwlo.trans_le hwX
  have hT : 0 ≤ delta * (X - w) := mul_nonneg hdelta0.le (sub_nonneg.mpr hwX)
  have hactive : 0 < (2 - delta) * (3 / 4 - X) -
      delta * (X - w) - (1 - X) / 12 := by
    have hp := mul_pos hdelta0 (sub_pos.mpr hw0)
    have hq := mul_le_mul_of_nonneg_right hh.1 hdelta0.le
    have hr := mul_nonneg (show 0 ≤ 2 / 5 - delta by linarith only [hdelta.2])
      (show 0 ≤ 29 / 100 by norm_num)
    nlinarith only [hdelta_w0, hp, hq, hr, hX]
  have hend := supportPolynomial_ge_endpoint (h := h) hdelta hXlo hX hT hV hVhi hactive
  have hXcoef : 0 ≤ 4 * delta - 8 / 25 := by linarith only [hdelta.1]
  have hfirstFactor : 0 < (4 * delta - 8 / 25) * (X + w) +
      14 / 25 - 81 * delta / 50 - (96 / 25) * delta * w := by
    have hp := mul_nonneg hXcoef (sub_nonneg.mpr hwX)
    have hq := mul_pos
      (show 0 < (104 / 25) * delta - 16 / 25 by linarith only [hdelta.1])
      (show 0 < w - 1 / 2 by linarith only [hwlo])
    nlinarith only [hp, hq, hdelta0]
  have hfirst := mul_nonneg (sub_nonneg.mpr hwX) hfirstFactor.le
  have hfirstId : squarePolynomial delta h X (3 / 4 - X) (delta * (X - w)) -
      referencePolynomial delta h w = (X - w) *
        ((4 * delta - 8 / 25) * (X + w) + 14 / 25 - 81 * delta / 50 -
          (96 / 25) * delta * w) := by
    unfold referencePolynomial squarePolynomial
    ring
  have hcoef : 0 ≤ 4 * (1 - delta) - (24 / 25) * (23 / 12 - delta) ^ 2 := by
    have hsq : delta ^ 2 ≤ (2 / 5 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hdelta0.le hdelta.2 2
    nlinarith only [hsq, hdelta.2]
  have hsecondFactor : 0 < delta + (1 - (w + w0) / 2) / 6 +
      (3 / 4 - (w + w0) / 2) *
        (4 * (1 - delta) - (24 / 25) * (23 / 12 - delta) ^ 2) +
      (23 / 12 - delta) / 50 := by
    have hwupper : w < 137 / 200 := hwX.trans_lt hX
    have hp := mul_nonneg (show 0 ≤ 3 / 4 - (w + w0) / 2 by linarith only [hw0, hwupper]) hcoef
    linarith only [hdelta0, hdelta.2, hw0, hwupper, hp]
  have hsecond := mul_pos (sub_pos.mpr hw0) hsecondFactor
  have hsecondId : referencePolynomial delta h w - referencePolynomial delta h w0 =
      (w - w0) * (delta + (1 - (w + w0) / 2) / 6 +
        (3 / 4 - (w + w0) / 2) *
          (4 * (1 - delta) - (24 / 25) * (23 / 12 - delta) ^ 2) +
        (23 / 12 - delta) / 50) := by
    unfold referencePolynomial squarePolynomial
    ring
  have hreference := reference_polynomial_pos hdelta hh
  change 0 < referencePolynomial delta h w0 at hreference
  linarith only [hend, hfirst, hfirstId, hsecond, hsecondId, hreference]

/-- A nonnegative bad star bounds the common-neighbor mass. The strict
threshold is applied before the division-free row comparison. -/
theorem nonnegative_bad_row_mass_cap {A beta delta ell gamma u missing D : ℝ}
    (hdelta : 0 < delta) (hell : 0 ≤ ell) (hbeta : 0 ≤ beta)
    (hmissing : 0 ≤ missing) (hu : u ≤ 1 - A)
    (hthreshold : A * (beta + delta) < 3 * gamma)
    (hmargin : 2 * A * delta < 3 * gamma) (hD : delta * D = delta - 2 * gamma)
    (hrow : gamma + ell * missing ≤ beta * (2 * A + u - 1) + delta * (D - u)) :
    delta * u ≤ delta - 3 * gamma := by
  have hp := mul_nonneg hell hmissing
  have hrow' : 3 * gamma + delta * u ≤ delta + beta * (2 * A + u - 1) := by
    nlinarith only [hrow, hD, hp]
  have hbetahi : beta < delta := by
    by_contra hn
    have hprod := mul_nonneg (show 0 ≤ beta - delta by linarith only [hn])
      (show 0 ≤ 1 - A - u by linarith only [hu])
    nlinarith only [hprod, hthreshold, hrow']
  by_contra hn
  have hprod := mul_pos (sub_pos.mpr hbetahi)
    (show 0 < delta * u - delta + 3 * gamma by linarith only [hn])
  have hscaled := mul_le_mul_of_nonneg_left hrow' hdelta.le
  have hmargin' := mul_nonneg hbeta (show 0 ≤ 3 * gamma - 2 * A * delta by
    linarith only [hmargin])
  nlinarith only [hprod, hscaled, hmargin']

/-- The same original bad-row bound gives a strict common-mass cap at a
negative star. Its strict old support bound is retained. -/
theorem negative_bad_row_mass_lt {A a delta ell gamma u missing D : ℝ}
    (hdelta : 0 < delta) (hell : 0 ≤ ell) (hsum : delta + ell = 1)
    (ha : 0 ≤ a) (haell : a < ell) (hmissing : 0 ≤ missing)
    (hmargin : 2 * A * delta < 3 * gamma) (hD : delta * D = delta - 2 * gamma)
    (hrow : gamma + ell * missing ≤ a * (1 - 2 * A - u) + delta * (D - u)) :
    u + ell * missing < 1 - 2 * ell * A - 3 * gamma := by
  have hp := mul_nonneg hell hmissing
  have hrow' : 3 * gamma + ell * missing + delta * u ≤
      delta + a * (1 - 2 * A - u) := by nlinarith only [hrow, hD]
  have hmass : 0 < 1 - 2 * A - u := by
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hn)
    have hscaled := mul_nonneg hdelta.le
      (show 0 ≤ u - (1 - 2 * A) by linarith only [hn])
    nlinarith only [hprod, hscaled, hp, hrow', hmargin]
  have hstrict := mul_pos (sub_pos.mpr haell) hmass
  have hdeltaeq : delta = 1 - ell := by linarith only [hsum]
  rw [hdeltaeq] at hrow'
  nlinarith only [hstrict, hrow']

/-- The sharp corner enclosure pays the ratio needed to detect a
negative original star. The common slope remains its own bracket value. -/
theorem corner_negative_ratio {ell gamma : ℝ}
    (hell : ell ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hfloor : 2 * (138261458236451 / 1116960975000000 : ℝ) -
      ell * (23243417 / 10 ^ 8) < gamma) :
    (3 / 8 : ℝ) * (1 - ell) * (1 + ell) < gamma * (1 + 2 * ell) := by
  have hfactor : 0 ≤ (ell - 363 / 589) *
      ((3 / 8 - 2 * (23243417 / 10 ^ 8 : ℝ)) * (ell + 363 / 589) +
        4 * (138261458236451 / 1116960975000000 : ℝ) - 23243417 / 10 ^ 8) := by
    apply mul_nonneg (sub_nonneg.mpr hell.1)
    nlinarith only [hell.2]
  have hmul := mul_pos (sub_pos.mpr hfloor)
    (show 0 < 1 + 2 * ell by linarith only [hell.1])
  nlinarith only [hfactor, hmul]

/-- The original square cap, sharp contact enclosure and actual trace
pay every initial mass and insertion guard used by the corner bad region. -/
theorem saturated_initial_guards {A ell gamma h c : ℝ}
    (hell : ell ∈ Icc (363 / 589 : ℝ) (9 / 11))
    (hc : 138261458236451 / 1116960975000000 < c)
    (hh : h < 23243417 / 10 ^ 8) (hA0 : 0 ≤ A) (hcA : c ≤ A ^ 2)
    (hfloor : 2 * (138261458236451 / 1116960975000000 : ℝ) -
      ell * (23243417 / 10 ^ 8) < gamma)
    (htrace : 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * h) :
    7 / 20 < A ∧ A < 3 / 8 ∧ 2 * A * (1 - ell) < 3 * gamma ∧
      ((21 / 100 < 1 - ell) →
        63 / 1000 < gamma ∧ 29 / 100 < 3 * gamma / A - (1 - ell)) := by
  have hAlow : 7 / 20 < A := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hA0 (sub_nonpos.mpr (le_of_not_gt hn))
    nlinarith only [hc, hcA, hp]
  have hgamma : 7 / 125 < gamma := by linarith only [hfloor, hell.2]
  have hAhi : A < 3 / 8 := by
    by_contra hn
    have hge : 3 / 8 ≤ A := le_of_not_gt hn
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 8) hge 2
    have hp : (3 / 8 : ℝ) * (7 / 125) < A * gamma := by
      calc
        _ ≤ A * (7 / 125) := mul_le_mul_of_nonneg_right hge (by norm_num)
        _ < A * gamma := mul_lt_mul_of_pos_left hgamma (by linarith only [hge])
    have hsq : (7 / 125 : ℝ) ^ 2 < gamma ^ 2 := by
      have hprod := mul_pos (sub_pos.mpr hgamma)
        (show 0 < gamma + 7 / 125 by linarith only [hgamma])
      nlinarith only [hprod]
    nlinarith only [htrace, hh, hsquare, hp, hsq]
  have hdelta : 0 < 1 - ell := by linarith only [hell.2]
  have hmargin : 2 * A * (1 - ell) < 3 * gamma := by
    have hp := mul_pos (sub_pos.mpr hAhi) hdelta
    have hline : (3 / 4 : ℝ) * (1 - ell) < 3 * gamma := by
      linarith only [hfloor, hell.1]
    nlinarith only [hp, hline]
  refine ⟨hAlow, hAhi, hmargin, ?_⟩
  intro hstrip
  have hcorrelated : (23 / 100 : ℝ) * (1 - ell) + 37 / 2500 < gamma := by
    linarith only [hfloor, hell.2]
  have hg63 : 63 / 1000 < gamma := by linarith only [hcorrelated, hstrip]
  refine ⟨hg63, ?_⟩
  have hprod := mul_pos (sub_pos.mpr hAhi)
    (show 0 < 29 / 100 + (1 - ell) by linarith only [hdelta])
  have hscaled : (29 / 100 + (1 - ell)) * A < 3 * gamma := by
    nlinarith only [hprod, hcorrelated, hstrip]
  have hdiv := (lt_div_iff₀ (show 0 < A by linarith only [hAlow])).mpr hscaled
  linarith only [hdiv]

/-- The certified exceptional boundary and its exact quadratic cover
all original legal excesses and exceptional masses. -/
theorem exceptional_price_pos {δ A E L r : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A))
    (hr : r ∈ Icc (0 : ℝ) E) (hEL : E ≤ L)
    (hLmax : L ≤ 2 - 5 * A - E) (hLr : L ≤ E + 6 * r) :
    0 < cornerExceptionalPrice δ A E L r := by
  let rstar := (2 - 5 * A - 2 * E) / 6
  have hδ0 : 0 ≤ δ := by linarith only [hδ.1]
  have hrstar : 0 ≤ rstar := by dsimp only [rstar]; linarith only [hEL, hLmax]
  have hgap := (exceptional_guards hδ hA hE).2.1
  have hcoef : 0 ≤ A + E - cornerBadCap δ A E - r := by linarith only [hgap, hr.2]
  have hmono {L' : ℝ} (hLL' : L ≤ L') :
      cornerExceptionalPrice δ A E L' r ≤ cornerExceptionalPrice δ A E L r := by
    have hid : cornerExceptionalPrice δ A E L r -
        cornerExceptionalPrice δ A E L' r =
          4 * δ * (L' - L) * (A + E - cornerBadCap δ A E - r) := by
      unfold cornerExceptionalPrice
      ring
    have hp : 0 ≤ 4 * δ * (L' - L) * (A + E - cornerBadCap δ A E - r) :=
      mul_nonneg (mul_nonneg (by linarith only [hδ0]) (sub_nonneg.mpr hLL')) hcoef
    linarith only [hid, hp]
  by_cases hrr : r ≤ rstar
  · exact (exceptional_boundary_price_pos hδ hA hE ⟨hr.1, hrr⟩).trans_le
      (hmono hLr)
  · have hrr' : rstar ≤ r := le_of_lt (lt_of_not_ge hrr)
    have hboundary := exceptional_boundary_price_pos hδ hA hE ⟨hrstar, le_rfl⟩
    have hLstar : E + 6 * rstar = 2 - 5 * A - E := by dsimp only [rstar]; ring
    rw [hLstar] at hboundary
    have hslope := exceptional_slope_pos hδ hA hE
    have hquadratic := exceptional_quadratic_coefficient_pos hδ
    have hdifference : cornerExceptionalPrice δ A E (2 - 5 * A - E) r -
        cornerExceptionalPrice δ A E (2 - 5 * A - E) rstar =
          (r - rstar) * (cornerExceptionalSlope δ A E +
            ((12 * δ ^ 2 + 54 * δ - 8) / 25) * (r + rstar)) := by
      rw [cornerExceptionalPrice_quadratic δ A E r, cornerExceptionalPrice_quadratic δ A E rstar]
      ring
    have hnonneg : 0 ≤ (r - rstar) * (cornerExceptionalSlope δ A E +
        ((12 * δ ^ 2 + 54 * δ - 8) / 25) * (r + rstar)) := by
      exact mul_nonneg (sub_nonneg.mpr hrr')
        (add_nonneg hslope.le (mul_nonneg hquadratic.le (add_nonneg hr.1 hrstar)))
    exact (show 0 < cornerExceptionalPrice δ A E (2 - 5 * A - E) r by
      linarith only [hboundary, hdifference, hnonneg]).trans_le (hmono hLmax)

/-- The certified small-excess endpoint controls every smaller positive
excess while the same bad-region cap is retained. -/
theorem small_excess_price_pos {δ A E L : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (3507 / 10000 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (cornerDeficitCap δ - A))
    (hL : L ∈ Icc (0 : ℝ) E) : 0 < cornerPrice δ A E L := by
  have hA' : A ∈ Icc (7 / 20 : ℝ) (3 / 8) := ⟨by linarith only [hA.1], hA.2⟩
  have hbase := small_L_price_pos hδ hA' hE
  have hgap := (exceptional_guards hδ hA hE).2.1
  have hδ0 : 0 ≤ δ := by linarith only [hδ.1]
  have hv : 0 ≤ EmptySatE2.baseDifference A (A + E) := by
    unfold EmptySatE2.baseDifference
    linarith only [hA.1, hE.1]
  have hm : 0 ≤ 2 - δ := by linarith only [hδ.2]
  have hD : 0 ≤ A + E := by linarith only [hA.1, hE.1]
  have hp : 0 ≤ (4 * (2 - δ) * EmptySatE2.baseDifference A (A + E) +
      8 * (A + E)) / 25 := by positivity
  have hg : 0 ≤ A + E - cornerBadCap δ A E := by linarith only [hgap, hE.1]
  have hid : cornerPrice δ A E L - cornerPrice δ A E E =
      (E - L) * ((4 * (2 - δ) * EmptySatE2.baseDifference A (A + E) +
        8 * (A + E)) / 25 + 8 * (E + L) / 25 +
        4 * δ * (A + E - cornerBadCap δ A E)) := by
    unfold cornerPrice cornerBadCap
    ring
  have hnonneg : 0 ≤ (E - L) *
      ((4 * (2 - δ) * EmptySatE2.baseDifference A (A + E) + 8 * (A + E)) / 25 +
        8 * (E + L) / 25 + 4 * δ * (A + E - cornerBadCap δ A E)) := by
    exact mul_nonneg (sub_nonneg.mpr hL.2)
      (add_nonneg (add_nonneg hp (div_nonneg (mul_nonneg (by norm_num)
          (add_nonneg hE.1 hL.1)) (by norm_num)))
        (mul_nonneg (by linarith only [hδ0]) hg))
  linarith only [hbase, hid, hnonneg]

/-- The two favorable correlations in the small-E certificate are
retained before concluding positivity of the actual joint price. -/
theorem small_E_price_pos {δ A E L : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (7 / 20 : ℝ) (3 / 8))
    (hE : E ∈ Icc (0 : ℝ) (1 / 20)) (hL : L ∈ Icc E (1 / 10))
    (hcap : A + E ≤ cornerDeficitCap δ) (htrace : 0 ≤ cornerTraceSlack δ A) :
    0 < cornerPrice δ A E L := by
  have hp := small_E_corrected_price_pos hδ hA hE hL
  linarith only [hp, hcap, htrace]

/-- The middle-deficit corrected certificate gives positivity with the
original nonnegative trace slack. -/
theorem middle_delta_price_pos {δ A E L : ℝ}
    (hδ : δ ∈ Icc (37 / 172 : ℝ) (1 / 4))
    (hA : A ∈ Icc (7 / 20 : ℝ) (cornerDeficitCap δ - 1 / 20))
    (hE : E ∈ Icc (1 / 20 : ℝ) (cornerDeficitCap δ - A))
    (hL : L ∈ Icc E (E + (3 * A - 1) / 2))
    (htrace : 0 ≤ cornerTraceSlack δ A) : 0 < cornerPrice δ A E L := by
  have hp := middle_delta_corrected_price_pos hδ hA hE hL
  linarith only [hp, htrace]

/-- The same private-source mean and strict original endpoint cap pay
the small-E and middle-deficit domains. -/
theorem nonexceptional_easy_price_pos {δ A E L j : ℝ}
    (hδ : δ ∈ Icc (21 / 100 : ℝ) (2 / 5))
    (hA : A ∈ Icc (7 / 20 : ℝ) (3 / 8))
    (hE : 0 < E) (hEL : E < L)
    (hcap : A + E ≤ cornerDeficitCap δ)
    (htrace : 0 ≤ cornerTraceSlack δ A)
    (hmean : (L + E) * L ≤ E * j) (hj : j < 3 * A - 1 + E + L)
    (heasy : E ≤ 1 / 20 ∨ δ ≤ 1 / 4) : 0 < cornerPrice δ A E L := by
  have hv : 0 < 3 * A - 1 := by linarith only [hA.1]
  have hEJ := mul_lt_mul_of_pos_left hj hE
  have hsquare : L ^ 2 < E * (3 * A - 1 + E) := by
    nlinarith only [hmean, hEJ]
  have hwidth : L - E < (3 * A - 1) / 2 := by
    by_contra hn
    have hL0 : 0 < L := hE.trans hEL
    have hp := mul_nonneg
      (show 0 ≤ L - (E + (3 * A - 1) / 2) by linarith only [hn])
      (show 0 ≤ L + (E + (3 * A - 1) / 2) by linarith only [hL0, hE, hv])
    nlinarith only [hsquare, hp, sq_nonneg (3 * A - 1)]
  by_cases hEsmall : E ≤ 1 / 20
  · have hLhi : L ≤ 1 / 10 := by
      by_contra hn
      have hL0 : 1 / 10 < L := lt_of_not_ge hn
      have hbound : E * (3 * A - 1 + E) ≤ (1 / 20 : ℝ) * (7 / 40) :=
        mul_le_mul hEsmall (by linarith only [hA.2, hEsmall])
          (by linarith only [hA.1, hE]) (by norm_num)
      nlinarith only [hsquare, hbound, hL0]
    exact small_E_price_pos hδ hA ⟨hE.le, hEsmall⟩ ⟨hEL.le, hLhi⟩ hcap htrace
  · have hδsmall := heasy.resolve_left hEsmall
    have hδ0 : 0 < δ := by linarith only [hδ.1]
    have hcap' := mul_le_mul_of_nonneg_left hcap hδ0.le
    have hid : δ * (37 / (1250 * δ)) = 37 / 1250 := by field_simp
    have hlow : 37 / 172 < δ := by
      unfold cornerDeficitCap at hcap'
      have hbound := mul_lt_mul_of_pos_left
        (show 2 / 5 < A + E by linarith only [hA.1, hEsmall]) hδ0
      nlinarith only [hcap', hbound, hid]
    exact middle_delta_price_pos ⟨hlow.le, hδsmall⟩
      ⟨hA.1, by linarith only [hcap, hEsmall]⟩
      ⟨by linarith only [hEsmall], by linarith only [hcap]⟩
      ⟨hEL.le, by linarith only [hwidth]⟩ htrace

end Erdos1017.EmptySatCorner
