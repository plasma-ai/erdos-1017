module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Corner peak above one third from the sharp count cells

The exact corner enclosure exceeds each scalar envelope, and the sharp
count-cell bounds force a corner peak above one third; this is the scalar
implication, with the endpoint, budget and corner premises derived in the model
wrapper.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CornerSelector

/-- The exact corner enclosure exceeds each scalar envelope used below. -/
theorem corner_floor_bounds {ell : ℝ} (hell : ell ∈ Set.Icc (363 / 589 : ℝ) (9 / 11)) :
    ((ell ≤ 2 / 3) →
      (2 - ell) / 16 < 2 * (138261458236451 / 1116960975000000 : ℝ) - ell * (23243417 / 10 ^ 8) ∧
      2 * (1 - ell) / 9 < 2 * (138261458236451 / 1116960975000000 : ℝ) - ell * (23243417 / 10 ^ 8)) ∧
    ((2 / 3 ≤ ell) →
      1 < 8 * (2 * ell + 1) *
        (2 * (138261458236451 / 1116960975000000 : ℝ) - ell * (23243417 / 10 ^ 8)) ∧
      (4 - 3 * ell) / 27 <
        2 * (138261458236451 / 1116960975000000 : ℝ) - ell * (23243417 / 10 ^ 8)) := by
  constructor
  · intro h
    constructor <;> linarith
  · intro h
    have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hell.2)
    constructor <;> nlinarith

/-- The genuine sharp count-cell bounds force a corner peak above one
third. This is a scalar implication; the actual model wrapper derives
all endpoint, budget and corner-contact premises separately. -/
theorem third_lt_of_sharp_cells {ell A C h gamma : ℝ}
    (hell : ell ∈ Set.Icc (363 / 589 : ℝ) (9 / 11)) (hA : 0 < A)
    (hsigma : 0 ≤ h - A ^ 2) (hC : C ≤ A ^ 2)
    (hforward : gamma ≤ 2 * C - ell * h)
    (hfloor : 2 * (138261458236451 / 1116960975000000 : ℝ) - ell * (23243417 / 10 ^ 8) < gamma)
    (hmiddle : (1 - A) / A ∈ Set.Icc (2 : ℝ) 3 →
      C ≤ A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) / 12 + (h - A ^ 2) / 3)
    (hlarge : 3 ≤ (1 - A) / A →
      C ≤ A ^ 2 * ((1 - A) / A) / 4 + (h - A ^ 2) / ((1 - A) / A)) :
    1 / 3 < A := by
  by_contra hn
  have hthird : A ≤ (1 / 3 : ℝ) := le_of_not_gt hn
  have hell0 : 0 < ell := by linarith [hell.1]
  have hcap : gamma ≤ (2 - ell) * A ^ 2 - ell * (h - A ^ 2) := by nlinarith
  have hfloorBounds := corner_floor_bounds hell
  by_cases hquarter : A ≤ (1 / 4 : ℝ)
  · by_cases hsmall : ell ≤ (2 / 3 : ℝ)
    · have hprod := mul_nonneg hell0.le hsigma
      have hsquare : A ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2 - ell by linarith)
      linarith [(hfloorBounds.1 hsmall).1]
    · have hell23 : (2 / 3 : ℝ) ≤ ell := (lt_of_not_ge hsmall).le
      have hT : 3 ≤ (1 - A) / A := (le_div_iff₀ hA).mpr (by linarith)
      have hT0 : 0 < (1 - A) / A := lt_of_lt_of_le (by norm_num) hT
      have hcl := hlarge hT
      have hcredit := mul_nonneg hsigma (show 0 ≤ ell * ((1 - A) / A) - 2 by nlinarith)
      have hdiv : (h - A ^ 2) / ((1 - A) / A) * ((1 - A) / A) = h - A ^ 2 :=
        div_mul_cancel₀ _ hT0.ne'
      have hscaled := mul_le_mul_of_nonneg_right hcl hT0.le
      have hidentity : A ^ 2 * ((1 - A) / A) = A - A ^ 2 := by field_simp
      have hbound : gamma ≤ A / 2 - (ell + 1 / 2) * A ^ 2 := by
        have hflow := mul_le_mul_of_nonneg_right hforward hT0.le
        rw [hidentity] at hscaled
        nlinarith
      have hden : 0 < 8 * (2 * ell + 1) := by positivity
      have hscaledGamma := mul_lt_mul_of_pos_left hfloor hden
      have hscaledBound := mul_le_mul_of_nonneg_left hbound hden.le
      have hsquare := sq_nonneg (4 * (ell + 1 / 2) * A - 1)
      nlinarith [(hfloorBounds.2 hell23).1]
  · have hquarter' : (1 / 4 : ℝ) ≤ A := (lt_of_not_ge hquarter).le
    have hT : (1 - A) / A ∈ Set.Icc (2 : ℝ) 3 := by
      constructor
      · exact (le_div_iff₀ hA).mpr (by linarith)
      · exact (div_le_iff₀ hA).mpr (by linarith)
    have hcm := hmiddle hT
    have hidentity : A ^ 2 * (6 * ((1 - A) / A) - ((1 - A) / A) ^ 2) =
        -1 + 8 * A - 7 * A ^ 2 := by field_simp; ring
    rw [hidentity] at hcm
    have hbound : gamma ≤ (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 +
        (2 / 3 - ell) * (h - A ^ 2) := by nlinarith
    by_cases hsmall : ell ≤ (2 / 3 : ℝ)
    · have hweight : 0 ≤ 1 - 3 * ell / 2 := by linarith
      have hfirst := mul_le_mul_of_nonneg_left hcap hweight
      have hsecond := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 3 * ell / 2 by positivity)
      have hJ : gamma ≤ (8 * A ^ 2 + 8 * ell * A - 23 * ell * A ^ 2 - ell) / 4 := by
        nlinarith
      have hfactor := mul_nonneg (show 0 ≤ 23 * ell - 8 by linarith [hell.1])
        (sub_nonneg.mpr hthird)
      have hbracket : 0 ≤ (8 - 23 * ell) * (A + 1 / 3) + 8 * ell := by nlinarith
      have hmono := mul_nonneg (sub_nonneg.mpr hthird) hbracket
      nlinarith [(hfloorBounds.1 hsmall).2]
    · have hell23 : (2 / 3 : ℝ) ≤ ell := (lt_of_not_ge hsmall).le
      have hcredit := mul_nonneg (sub_nonneg.mpr hell23) hsigma
      have hproduct := mul_le_mul
        (show 7 + 6 * ell ≤ (131 / 11 : ℝ) by linarith [hell.2])
        (show A + 1 / 3 ≤ (2 / 3 : ℝ) by linarith)
        (show 0 ≤ A + 1 / 3 by linarith) (by norm_num : (0 : ℝ) ≤ 131 / 11)
      have hbracket : 0 ≤ 8 - (7 + 6 * ell) * (A + 1 / 3) := by linarith
      have hmono := mul_nonneg (sub_nonneg.mpr hthird) hbracket
      nlinarith [(hfloorBounds.2 hell23).2]

end Erdos1017.CornerSelector
