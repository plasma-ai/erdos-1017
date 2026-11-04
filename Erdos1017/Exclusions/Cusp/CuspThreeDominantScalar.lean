module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Scalar bounds for the dominant missing atom

A dominant missing atom cannot satisfy the necessary copy inequality, the whole
remainder being paid through its mass `r`; the dominant-atom interval bound
keeps the sign of the radical before squaring and includes both endpoints.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Erdos1017.CuspThreeDominantScalar

private def radicalCoefficient (B : ℝ) : ℝ :=
  8 * (19 / 20) * (B - 11 / 39) * (1 / 27 - (B - 11 / 39) / 20)

private def signPolynomial (B : ℝ) : ℝ :=
  radicalCoefficient B * (11 / 39) -
    (1 - B) * ((41 / 20) * (B - 11 / 39) - 1 / 27) ^ 2

private def squarePolynomial (B : ℝ) : ℝ :=
  signPolynomial B ^ 2 - radicalCoefficient B ^ 2 * (2 * (1 / 9 - B ^ 2))

private theorem bernstein_sum_pos (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : ∀ i, 1 ≤ c i) (x : I) :
    0 < ∑ i, c i * bernstein n i x := by
  have hsum : 1 ≤ ∑ i, c i * bernstein n i x := by
    rw [← bernstein.probability n x]
    apply Finset.sum_le_sum
    intro i _
    exact (one_mul _).symm.trans_le
      (mul_le_mul_of_nonneg_right (hc i) bernstein_nonneg)
  linarith only [hsum]

private theorem sign_chart (x : I) :
    0 < signPolynomial (2339 / 7371 + (1 / 3 - 2339 / 7371) * x) := by
  let coeff : Fin 4 → ℝ := ![36397192000, 33656026040, 26071396680, 13988546019]
  have hpos := bernstein_sum_pos 3 coeff
    (by intro i; fin_cases i <;> norm_num [coeff]) x
  have hid : (20023926290550 : ℝ) *
      signPolynomial (2339 / 7371 + (1 / 3 - 2339 / 7371) * x) =
      ∑ i : Fin 4, coeff i * bernstein 3 i x := by
    norm_num [signPolynomial, radicalCoefficient, coeff, Fin.sum_univ_succ,
      bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 800000 in
private theorem square_chart (x : I) :
    0 < squarePolynomial (2339 / 7371 + (1 / 3 - 2339 / 7371) * x) := by
  let coeff : Fin 7 → ℝ :=
    ![963123303064000000000, 820300868673832000000, 625590720337272872000,
      412910421311942124480, 238615607785377994416, 178689175142727067560,
      326132366209467913935]
  have hpos := bernstein_sum_pos 6 coeff
    (by intro i; fin_cases i <;> norm_num [coeff]) x
  have hid : (668262706815632471698837500 : ℝ) *
      squarePolynomial (2339 / 7371 + (1 / 3 - 2339 / 7371) * x) =
      ∑ i : Fin 7, coeff i * bernstein 6 i x := by
    norm_num [squarePolynomial, signPolynomial, radicalCoefficient, coeff,
      Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

/-- The exact dominant-atom interval certificate keeps the radical's sign
before squaring and includes both ends of the original closed interval. -/
theorem limiting_radical_bound {B : ℝ}
    (hB : B ∈ Set.Icc (2339 / 7371 : ℝ) (1 / 3)) :
    (1 - B) * ((41 / 20) * (B - 11 / 39) - 1 / 27) ^ 2 <
      8 * (19 / 20) * (B - 11 / 39) * (1 / 27 - (B - 11 / 39) / 20) *
        (11 / 39 - Real.sqrt (2 * (1 / 9 - B ^ 2))) := by
  let x : I := ⟨(B - 2339 / 7371) / (1 / 3 - 2339 / 7371), by
    constructor <;> norm_num <;> linarith only [hB.1, hB.2]⟩
  have hx : 2339 / 7371 + (1 / 3 - 2339 / 7371) * (x : ℝ) = B := by
    dsimp [x]
    ring
  have hsign := sign_chart x
  have hsquare := square_chart x
  rw [hx] at hsign hsquare
  have hrad : 0 ≤ 2 * (1 / 9 - B ^ 2) := by
    nlinarith only [hB.1, hB.2]
  have hs := Real.sq_sqrt hrad
  have hcoeff : 0 ≤ radicalCoefficient B := by
    unfold radicalCoefficient
    have hfirst : 0 ≤ B - 11 / 39 := by linarith only [hB.1]
    have hsecond : 0 ≤ 1 / 27 - (B - 11 / 39) / 20 := by linarith only [hB.2]
    positivity
  have hroot : radicalCoefficient B * Real.sqrt (2 * (1 / 9 - B ^ 2)) <
      signPolynomial B := by
    apply (sq_lt_sq₀ (mul_nonneg hcoeff (Real.sqrt_nonneg _)) hsign.le).mp
    rw [mul_pow, hs]
    exact sub_pos.mp hsquare
  dsimp [signPolynomial, radicalCoefficient] at hroot
  linarith only [hroot]

private theorem ratio_cross {b B : ℝ} (hb : 0 < b) (hbB : b ≤ B)
    (hlarge : 1 / 27 ≤ (21 / 20) * b) :
    ((41 / 20) * b - 1 / 27) ^ 2 * (B * (1 / 27 - B / 20)) ≤
      ((41 / 20) * B - 1 / 27) ^ 2 * (b * (1 / 27 - b / 20)) := by
  have hfirst := mul_nonneg
    (show 0 ≤ (41 / 20) * b - 1 / 27 by linarith only [hlarge, hb])
    (show 0 ≤ (39 / 20) * b + 1 / 27 by positivity)
  have hsecond := mul_nonneg (sub_nonneg.mpr hbB)
    (show 0 ≤ (1599 / 400) * b + 1 / 540 by positivity)
  have hbracket : 0 ≤ (1599 / 400) * b * B + (b + B) / 540 - 1 / 729 := by
    nlinarith only [hfirst, hsecond]
  have hpaid := mul_nonneg (sub_nonneg.mpr hbB) hbracket
  nlinarith only [hpaid]

set_option maxHeartbeats 800000 in
/-- A dominant missing atom cannot satisfy the necessary copy inequality.
The entire remainder is paid through its original mass `r`. -/
theorem dominant_contradiction {A b r : ℝ}
    (hA : 11 / 39 ≤ A) (hb : 0 < b) (hrcap : r ≤ b / 20)
    (hmass : A + b ≤ 1 / 3) (hlarge : 1 / 27 ≤ b + r)
    (hcopy : 8 * (b - r) * (1 / 27 - r) *
        (A - Real.sqrt (2 * (1 / 9 - (A + b) ^ 2))) ≤
      (1 - A - b) * (2 * b - 1 / 27 + r) ^ 2) : False := by
  let B := A + b
  let b₀ := B - 11 / 39
  let s := Real.sqrt (2 * (1 / 9 - B ^ 2))
  let D := b * (1 / 27 - b / 20)
  let D₀ := b₀ * (1 / 27 - b₀ / 20)
  let N := ((41 / 20) * b - 1 / 27) ^ 2
  let N₀ := ((41 / 20) * b₀ - 1 / 27) ^ 2
  have hbcap : b ≤ 2 / 39 := by linarith only [hA, hmass]
  have hbb₀ : b ≤ b₀ := by dsimp [b₀, B]; linarith only [hA]
  have hb₀ : 0 < b₀ := hb.trans_le hbb₀
  have hb₀cap : b₀ ≤ 2 / 39 := by dsimp [b₀, B]; linarith only [hmass]
  have hlarge' : 1 / 27 ≤ (21 / 20) * b := by linarith only [hlarge, hrcap]
  have hB : B ∈ Set.Icc (2339 / 7371 : ℝ) (1 / 3) := by
    dsimp [B]
    constructor <;> linarith only [hlarge', hA, hmass]
  have hrad : 0 ≤ 2 * (1 / 9 - B ^ 2) := by nlinarith only [hB.1, hB.2]
  have hs : s ^ 2 = 2 * (1 / 9 - B ^ 2) := Real.sq_sqrt hrad
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsL : s < 11 / 39 := by nlinarith only [hs, hs0, hB.1]
  have hd : 0 < A - s := by linarith only [hsL, hA]
  have hD : 0 < D := mul_pos hb (by linarith only [hbcap])
  have hD₀ : 0 < D₀ := mul_pos hb₀ (by linarith only [hb₀cap])
  have hB1 : 0 ≤ 1 - B := by linarith only [hB.2]
  have hcoefficient : 8 * (19 / 20) * D ≤ 8 * (b - r) * (1 / 27 - r) := by
    have hprod := mul_le_mul
      (show (19 / 20) * b ≤ b - r by linarith only [hrcap])
      (show 1 / 27 - b / 20 ≤ 1 / 27 - r by linarith only [hrcap])
      (show 0 ≤ 1 / 27 - b / 20 by linarith only [hbcap])
      (show 0 ≤ b - r by linarith only [hb, hrcap])
    dsimp [D]
    nlinarith only [hprod]
  have hnum : (2 * b - 1 / 27 + r) ^ 2 ≤ N := by
    have hleft : 0 ≤ 2 * b - 1 / 27 + r := by linarith only [hlarge, hb]
    have hright : 2 * b - 1 / 27 + r ≤ (41 / 20) * b - 1 / 27 := by
      linarith only [hrcap]
    exact (sq_le_sq₀ hleft (hleft.trans hright)).mpr hright
  have hpaid : 8 * (19 / 20) * D * (A - s) ≤ (1 - B) * N := by
    calc
      _ ≤ 8 * (b - r) * (1 / 27 - r) * (A - s) :=
        mul_le_mul_of_nonneg_right hcoefficient hd.le
      _ ≤ (1 - B) * (2 * b - 1 / 27 + r) ^ 2 := by
        convert hcopy using 1
        dsimp [s, B]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnum hB1
  have hratio : N * D₀ ≤ N₀ * D := ratio_cross hb hbb₀ hlarge'
  have hpaid₀ : 8 * (19 / 20) * D₀ * (11 / 39 - s) ≤ (1 - B) * N₀ := by
    apply (mul_le_mul_iff_right₀ hD).mp
    calc
      D * (8 * (19 / 20) * D₀ * (11 / 39 - s)) ≤
          D * (8 * (19 / 20) * D₀ * (A - s)) := by
        gcongr
      _ = (8 * (19 / 20) * D * (A - s)) * D₀ := by ring
      _ ≤ ((1 - B) * N) * D₀ := mul_le_mul_of_nonneg_right hpaid hD₀.le
      _ = (1 - B) * (N * D₀) := by ring
      _ ≤ (1 - B) * (N₀ * D) := mul_le_mul_of_nonneg_left hratio hB1
      _ = D * ((1 - B) * N₀) := by ring
  have hlim := limiting_radical_bound hB
  change (1 - B) * N₀ < 8 * (19 / 20) * b₀ * (1 / 27 - b₀ / 20) *
    (11 / 39 - s) at hlim
  dsimp [D₀] at hpaid₀
  nlinarith only [hlim, hpaid₀]

end Erdos1017.CuspThreeDominantScalar
