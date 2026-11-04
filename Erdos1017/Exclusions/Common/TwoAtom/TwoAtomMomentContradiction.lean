module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Moment contradiction for the integer family

The remaining integer family cannot satisfy its three normalized stationary rows
together with the factorial-moment inequality; the rows are written after
multiplication by a positive factor, and the parameter `w` with the scaled and
eliminated equations is carried explicitly.
-/

@[expose] public section

namespace Erdos1017.TwoAtomCountGate

private def familyD (j w : ℝ) : ℝ := j ^ 2 * (w - 1) - j + w ^ 2 - 5 * w + 6

private def familyH (j w : ℝ) : ℝ := j * (j + 1) - 2 + w

private def familyP (j w : ℝ) : ℝ :=
  (2 * w ^ 2 - 2 * w + 1) * j ^ 2 + (2 * w ^ 2 - 4 * w - 1) * j +
    2 * w ^ 3 - 6 * w ^ 2 + 2 * w + 4

private theorem family_elimination (j w a b u : ℝ)
    (hBE : b - u - w = 0)
    (hBA : familyH j w * (b - a) - 2 * j * u - (familyH j w - 1) = 0)
    (hAR : (j * (j + 1) - 2 * j + 2 * w - 4) * a +
      (2 * j - j * (j + 1)) * b + 2 * (j - 1) * u +
      j * (j + 1) - 2 * j + 2 * w - 2 = 0) :
    2 * familyD j w * (u - 1) + familyP j w = 0 ∧
      familyH j w * (b - a - 1) = 2 * j * u - 1 := by
  constructor
  · dsimp [familyD, familyH, familyP] at *
    linear_combination (j * (j + 1) - 2 + w) * hAR +
      (j * (j + 1) - 2 * j + 2 * w - 4) * hBA -
      (j * (j + 1) - 2 + w) * (2 * w - 4) * hBE
  · linarith only [hBA]

private theorem family_moment_identity (j w a b u : ℝ)
    (hload : familyH j w * (b - a - 1) = 2 * j * u - 1) :
    familyH j w * (u ^ 2 - 2 * (1 - w) - (j - 1) * u * (b - a - 1)) =
      -(j * (j - 3) + 2 - w) * u ^ 2 + (j - 1) * u -
        2 * (1 - w) * familyH j w := by
  dsimp [familyH] at *
  linear_combination -(j - 1) * u * hload

private theorem familyP_pos {j w : ℝ} (hj : 4 ≤ j) (hw : 0 < w) :
    0 < familyP j w := by
  have hbase : 0 < 2 * w ^ 3 + 34 * (w - 23 / 34) ^ 2 + 15 / 34 := by
    positivity
  have hfirst : 0 ≤ (j - 4) ^ 2 * ((2 * w - 1) ^ 2 + 1) / 2 := by
    positivity
  have hsecond : 0 ≤ (j - 4) * (18 * (w - 5 / 9) ^ 2 + 13 / 9) := by
    exact mul_nonneg (by linarith) (by positivity)
  have hid : familyP j w =
      (2 * w ^ 3 + 34 * (w - 23 / 34) ^ 2 + 15 / 34) +
      (j - 4) ^ 2 * ((2 * w - 1) ^ 2 + 1) / 2 +
      (j - 4) * (18 * (w - 5 / 9) ^ 2 + 13 / 9) := by
    dsimp [familyP]
    ring
  rw [hid]
  linarith

private theorem familyD_neg {j w : ℝ} (hj : 4 ≤ j) (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
    familyD j w < 0 := by
  have hs : 0 ≤ j ^ 2 + w - 4 := by nlinarith [sq_nonneg (j - 4), hw.1]
  have hm := mul_nonneg (sub_nonneg.mpr hw.2.le) hs
  have hid : familyD j w = 2 - j - (1 - w) * (j ^ 2 + w - 4) := by
    dsimp [familyD]
    ring
  rw [hid]
  linarith

private theorem large_family_contradiction {j w a b u : ℝ}
    (hj : 4 ≤ j) (hw : w ∈ Set.Ioo (0 : ℝ) 1)
    (hvalue : 2 * familyD j w * (u - 1) + familyP j w = 0)
    (hload : familyH j w * (b - a - 1) = 2 * j * u - 1)
    (hmoment : 0 ≤ u ^ 2 - 2 * (1 - w) - (j - 1) * u * (b - a - 1)) : False := by
  have hD := familyD_neg hj hw
  have hP := familyP_pos hj hw.1
  have hu : 1 < u := by
    by_contra hn
    have hp := mul_nonneg_of_nonpos_of_nonpos hD.le (sub_nonpos.mpr (le_of_not_gt hn))
    nlinarith only [hp, hP, hvalue]
  have hH : 0 < familyH j w := by
    dsimp [familyH]
    nlinarith [hw.1, sq_nonneg (j - 4)]
  have hcoef : j - 1 < j * (j - 3) + 2 - w := by
    have hm := mul_nonneg (sub_nonneg.mpr hj) (by linarith : 0 ≤ j)
    nlinarith [hw.2]
  have hcoef0 : 0 < j * (j - 3) + 2 - w := by linarith
  have husq : u < u ^ 2 := by nlinarith
  have hprod := mul_lt_mul_of_pos_left husq hcoef0
  have hlinear := mul_lt_mul_of_pos_right hcoef (by linarith : 0 < u)
  have hnegative := mul_pos (sub_pos.mpr hw.2) hH
  have hnonneg := mul_nonneg hH.le hmoment
  rw [family_moment_identity j w a b u hload] at hnonneg
  nlinarith only [hprod, hlinear, hnegative, hnonneg]

private theorem three_family_contradiction {w a b u : ℝ}
    (hw : w ∈ Set.Ioo (0 : ℝ) 1)
    (hvalue : 2 * familyD 3 w * (u - 1) + familyP 3 w = 0)
    (hload : familyH 3 w * (b - a - 1) = 6 * u - 1)
    (hmoment : 0 ≤ u ^ 2 - 2 * (1 - w) - 2 * u * (b - a - 1)) : False := by
  have hU : (w ^ 2 + 4 * w - 6) * u + (w ^ 3 + 8 * w ^ 2 - 18 * w + 11) = 0 := by
    dsimp [familyD, familyP] at hvalue
    nlinarith only [hvalue]
  have hH : 0 < familyH 3 w := by dsimp [familyH]; linarith [hw.1]
  have hmoment' : 0 ≤ familyH 3 w *
      (u ^ 2 - 2 * (1 - w) - 2 * u * (b - a - 1)) := mul_nonneg hH.le hmoment
  have hid := family_moment_identity 3 w a b u
    (by simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using hload)
  norm_num only at hid
  rw [hid] at hmoment'
  let Q := u * w ^ 3 + 2 * u * w ^ 2 - 14 * u * w + 12 * u -
    w ^ 4 - 6 * w ^ 3 + 36 * w ^ 2 - 39 * w + 10
  have helim : (w ^ 2 + 4 * w - 6) ^ 2 *
      (-(2 - w) * u ^ 2 + 2 * u - 2 * (1 - w) * familyH 3 w) =
      familyH 3 w * (w - 1) ^ 2 *
        (w ^ 4 + 8 * w ^ 3 - 17 * w ^ 2 + 64 * w - 83) := by
    dsimp [familyH] at *
    linear_combination Q * hU
  have hquartic : w ^ 4 + 8 * w ^ 3 - 17 * w ^ 2 + 64 * w - 83 < 0 := by
    let z := 1 - w
    have hz : 0 < z ∧ z < 1 := by dsimp [z]; constructor <;> linarith [hw.1, hw.2]
    have hzsq : z ^ 2 ≤ z := by nlinarith
    have hzfour : z ^ 4 ≤ z ^ 2 := by nlinarith [sq_nonneg (z ^ 2)]
    have hzcube : 0 ≤ z ^ 3 := pow_nonneg hz.1.le 3
    have hid : w ^ 4 + 8 * w ^ 3 - 17 * w ^ 2 + 64 * w - 83 =
        z ^ 4 - 12 * z ^ 3 + 13 * z ^ 2 - 58 * z - 27 := by dsimp [z]; ring
    rw [hid]
    nlinarith only [hzsq, hzfour, hzcube, hz.1]
  have hsquare : 0 < (w - 1) ^ 2 := sq_pos_of_ne_zero (by linarith [hw.2])
  have hright := mul_neg_of_pos_of_neg (mul_pos hH hsquare) hquartic
  have hleft := mul_nonneg (sq_nonneg (w ^ 2 + 4 * w - 6)) hmoment'
  rw [helim] at hleft
  linarith

/-- The final integer family cannot satisfy its three normalized
stationary rows and the factorial-moment inequality. The rows are written
after multiplication by the positive denominator `j * (j + 1)`; the
elimination identities and their signs are proved inside this theorem.
This is a scalar result, not a physical-model extraction theorem. -/
theorem integer_family_moment_contradiction {j : ℕ} (hj : 3 ≤ j)
    {w a b u : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1)
    (hBE : b - u - w = 0)
    (hBA : ((j : ℝ) * (j + 1) - 2 + w) * (b - a) - 2 * j * u -
      ((j : ℝ) * (j + 1) - 3 + w) = 0)
    (hAR : ((j : ℝ) * (j + 1) - 2 * j + 2 * w - 4) * a +
      (2 * j - (j : ℝ) * (j + 1)) * b + 2 * ((j : ℝ) - 1) * u +
      (j : ℝ) * (j + 1) - 2 * j + 2 * w - 2 = 0)
    (hmoment : 0 ≤ u ^ 2 - 2 * (1 - w) - ((j : ℝ) - 1) * u * (b - a - 1)) :
    False := by
  have hBA' : familyH j w * (b - a) - 2 * j * u - (familyH j w - 1) = 0 := by
    dsimp [familyH]
    nlinarith only [hBA]
  obtain ⟨hvalue, hload⟩ := family_elimination j w a b u hBE hBA' hAR
  by_cases hthree : j = 3
  · subst j
    norm_num only [Nat.cast_ofNat] at hvalue hload hmoment
    exact three_family_contradiction hw hvalue hload
      (by norm_num at hmoment ⊢; exact hmoment)
  · have hjfour : (4 : ℝ) ≤ j := by exact_mod_cast (show 4 ≤ j by omega)
    exact large_family_contradiction hjfour hw hvalue hload hmoment

/-- The three stationary-row equations for the integer family
already contradict the physical factorial-moment bound. The parameter
`w` and all scaled and eliminated equations are constructed internally. -/
theorem stationary_integer_family_contradiction {j : ℕ} (hj : 3 ≤ j)
    {a b u ell : ℝ}
    (hell : ell ∈ Set.Ioo (1 - 4 / ((j : ℝ) * (j + 1)))
      (1 - 2 / ((j : ℝ) * (j + 1))))
    (hBE : (2 / ((j : ℝ) * (j + 1))) * b =
      ell - (1 - 4 / ((j : ℝ) * (j + 1))) + (2 / ((j : ℝ) * (j + 1))) * u)
    (hBA : (1 + ell) * (b - a) =
      (4 * j / ((j : ℝ) * (j + 1))) * u + ell + 1 - 2 / ((j : ℝ) * (j + 1)))
    (hAR : (ell - 2 * j / ((j : ℝ) * (j + 1))) * a +
      (2 * j / ((j : ℝ) * (j + 1)) - 1) * b +
      (2 * ((j : ℝ) - 1) / ((j : ℝ) * (j + 1))) * u +
      (ell - 2 * ((j : ℝ) - 1) / ((j : ℝ) * (j + 1))) = 0)
    (hmoment : 0 ≤ u ^ 2 - 2 * (1 - (ell - (1 - 4 / ((j : ℝ) * (j + 1)))) *
      ((j : ℝ) * (j + 1)) / 2) - ((j : ℝ) - 1) * u * (b - a - 1)) : False := by
  let x : ℝ := j
  let J := x * (x + 1)
  let w := (ell - (1 - 4 / J)) * J / 2
  have hx : 3 ≤ x := by dsimp [x]; exact_mod_cast hj
  have hJ : 0 < J := by dsimp [J]; positivity
  have hJne : J ≠ 0 := hJ.ne'
  have hwEq : 2 * w = (ell - 1) * J + 4 := by
    dsimp [w]
    field_simp
    ring
  have hlo : J - 4 < ell * J := by
    calc
      J - 4 = (1 - 4 / J) * J := by field_simp
      _ < ell * J := mul_lt_mul_of_pos_right hell.1 hJ
  have hhi : ell * J < J - 2 := by
    calc
      ell * J < (1 - 2 / J) * J := mul_lt_mul_of_pos_right hell.2 hJ
      _ = J - 2 := by field_simp
  have hw : w ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith only [hwEq, hlo, hhi]
  have hBE' : 2 * b - (ell - 1) * J - 4 - 2 * u = 0 := by
    change 2 / J * b = ell - (1 - 4 / J) + 2 / J * u at hBE
    field_simp at hBE
    nlinarith only [hBE]
  have hBA' : J * (1 + ell) * (b - a) - 4 * x * u - J * (ell + 1) + 2 = 0 := by
    change (1 + ell) * (b - a) = 4 * x / J * u + ell + 1 - 2 / J at hBA
    field_simp at hBA
    nlinarith only [hBA]
  have hAR' : (ell * J - 2 * x) * a + (2 * x - J) * b +
      2 * (x - 1) * u + ell * J - 2 * (x - 1) = 0 := by
    change (ell - 2 * x / J) * a + (2 * x / J - 1) * b +
      (2 * (x - 1) / J) * u + (ell - 2 * (x - 1) / J) = 0 at hAR
    field_simp at hAR
    nlinarith only [hAR]
  apply integer_family_moment_contradiction hj (a := a) (b := b) (u := u) hw
  · nlinarith only [hBE', hwEq]
  · change (J - 2 + w) * (b - a) - 2 * x * u - (J - 3 + w) = 0
    linear_combination hBA' / 2 + (b - a - 1) / 2 * hwEq
  · change (J - 2 * x + 2 * w - 4) * a + (2 * x - J) * b +
        2 * (x - 1) * u + J - 2 * x + 2 * w - 2 = 0
    linear_combination hAR' + (a + 1) * hwEq
  · exact hmoment

end Erdos1017.TwoAtomCountGate
