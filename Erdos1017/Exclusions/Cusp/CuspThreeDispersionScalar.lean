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
# Scalar contradiction for the dispersed low-slope domain

The dispersed-region coefficient lies strictly below its necessary lower ratio,
with every radical comparison licensed before squaring, and the two bounds on
the same source tax contradict the necessary body-to-hole ratio throughout the
dispersed low-slope domain.
-/

@[expose] public section

noncomputable section

open scoped BigOperators unitInterval

namespace Erdos1017.CuspThreeDispersionScalar

private def radicand (B : ℝ) : ℝ := 2 * (1 / 9 - B ^ 2 - B / 567)

private def signPolynomial (B : ℝ) : ℝ :=
  (439 / 315) * (11 / 39) * (B - 11 / 39) -
    2 * (1 - B) * (B - 11 / 39 - 1 / 27)

private def squarePolynomial (B : ℝ) : ℝ :=
  signPolynomial B ^ 2 - (439 / 315) ^ 2 * (B - 11 / 39) ^ 2 * radicand B

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
    0 < signPolynomial (112 / 351 + (5 / 351) * x) := by
  let coeff : Fin 3 → ℝ := ![125554, 66049, 10044]
  have hpos := bernstein_sum_pos 2 coeff
    (by intro i; fin_cases i <;> norm_num [coeff]) x
  have hid : (8624070 : ℝ) * signPolynomial (112 / 351 + (5 / 351) * x) =
      ∑ i : Fin 3, coeff i * bernstein 2 i x := by
    norm_num [signPolynomial, coeff, Fin.sum_univ_succ, bernstein_apply, Nat.choose]
    ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

set_option maxHeartbeats 1200000 in
private theorem square_chart (j : Fin 4) (x : I) :
    0 < squarePolynomial (112 / 351 + (5 / 1404) * ((j : ℕ) + (x : ℝ))) := by
  let coeff : Fin 4 → Fin 5 → ℝ :=
    ![![669711136372096, 571280072081056, 482709053535516, 403947735554601, 334950907076811],
      ![334950907076811, 265954078599021, 206721739624356, 157208679091316, 117374820057776],
      ![117374820057776, 77540961024236, 47386303490196, 26870770513531, 15959419271491],
      ![15959419271491, 5048068029451, 3740898522036, 12002967926496, 29804467539456]]
  have hpos := bernstein_sum_pos 4 (coeff j)
    (by intro i; fin_cases j <;> fin_cases i <;> norm_num [coeff]) x
  have hid : (4048357321718236800 : ℝ) *
      squarePolynomial (112 / 351 + (5 / 1404) * ((j : ℕ) + (x : ℝ))) =
      ∑ i : Fin 5, coeff j i * bernstein 4 i x := by
    fin_cases j <;> norm_num [squarePolynomial, signPolynomial, radicand, coeff,
      Fin.sum_univ_succ, bernstein_apply, Nat.choose] <;> ring
  rw [← hid] at hpos
  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hpos

private theorem square_pos_on_quarter (j : Fin 4) {B : ℝ}
    (hlo : 112 / 351 + (5 / 1404) * (j : ℕ) ≤ B)
    (hhi : B ≤ 112 / 351 + (5 / 1404) * ((j : ℕ) + 1)) :
    0 < squarePolynomial B := by
  let x : I := ⟨(B - 112 / 351) / (5 / 1404) - (j : ℕ), by
    constructor <;> norm_num <;> linarith only [hlo, hhi]⟩
  have hx : 112 / 351 + (5 / 1404) * ((j : ℕ) + (x : ℝ)) = B := by
    dsimp [x]
    ring
  simpa only [hx] using square_chart j x

private theorem sign_and_square_pos {B : ℝ}
    (hB : B ∈ Set.Icc (112 / 351 : ℝ) (1 / 3)) :
    0 < signPolynomial B ∧ 0 < squarePolynomial B := by
  let x : I := ⟨(B - 112 / 351) / (5 / 351), by
    constructor <;> norm_num <;> linarith only [hB.1, hB.2]⟩
  have hx : 112 / 351 + (5 / 351) * (x : ℝ) = B := by dsimp [x]; ring
  refine ⟨by simpa only [hx] using sign_chart x, ?_⟩
  by_cases h₀ : B ≤ 151 / 468
  · exact square_pos_on_quarter 0 (by norm_num; exact hB.1) (by norm_num; exact h₀)
  by_cases h₁ : B ≤ 229 / 702
  · exact square_pos_on_quarter 1 (by norm_num; linarith only [h₀]) (by norm_num; exact h₁)
  by_cases h₂ : B ≤ 463 / 1404
  · exact square_pos_on_quarter 2 (by norm_num; linarith only [h₁]) (by norm_num; exact h₂)
  exact square_pos_on_quarter 3 (by norm_num; linarith only [h₂]) (by norm_num; exact hB.2)

/-- The dispersed-region coefficient is strictly below its necessary
lower ratio. Every radical comparison is licensed before squaring. -/
theorem limiting_ratio_lt {B : ℝ}
    (hB : B ∈ Set.Icc (112 / 351 : ℝ) (1 / 3))
    (hrad : 0 ≤ 2 * (1 / 9 - B ^ 2 - B / 567)) :
    2 * (1 - B) * (B - 11 / 39 - 1 / 27) /
        ((B - 11 / 39) * (11 / 39 - Real.sqrt (2 * (1 / 9 - B ^ 2 - B / 567)))) <
      439 / 315 := by
  obtain ⟨hsgn, hsq⟩ := sign_and_square_pos hB
  let s := Real.sqrt (2 * (1 / 9 - B ^ 2 - B / 567))
  have hs : s ^ 2 = 2 * (1 / 9 - B ^ 2 - B / 567) := Real.sq_sqrt hrad
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hD : 0 < B - 11 / 39 := by linarith only [hB.1]
  have hsL : s < 11 / 39 := by nlinarith only [hs, hs0, hB.1]
  have hden : 0 < (B - 11 / 39) * (11 / 39 - s) := mul_pos hD (sub_pos.mpr hsL)
  have hroot : (439 / 315) * (B - 11 / 39) * s < signPolynomial B := by
    apply (sq_lt_sq₀ (by positivity) hsgn.le).mp
    rw [mul_pow, mul_pow, hs]
    exact sub_pos.mp hsq
  apply (div_lt_iff₀ hden).mpr
  dsimp [signPolynomial] at hroot
  linarith only [hroot]

set_option maxHeartbeats 800000 in
/-- The two bounds on the same original source tax contradict the required
body-to-hole ratio throughout the dispersed low-slope domain. -/
theorem dispersed_contradiction {A t H gamma L X v V : ℝ}
    (hA : 11 / 39 ≤ A) (ht : 1 / 27 < t) (hmass : A + t ≤ 1 / 3)
    (hH : 0 ≤ H) (hHcap : H ≤ 1 / 9 - (A + t) ^ 2 - (A + t) / 567)
    (hgamma : 1 / 27 ≤ gamma) (hgt : gamma < t) (htg : t ≤ 2 * gamma)
    (hv : 0 < v) (hX : 0 < X) (hVcap : V ≤ t * (1 - A - t))
    (hL : (439 / 315) * v ≤ L)
    (hcopy : (A - Real.sqrt (2 * H)) * X + gamma * L ≤ t * L)
    (hmixed : ((A - Real.sqrt (2 * H)) * X + gamma * L) ^ 2 ≤ 2 * v * V * X) :
    False := by
  let B := A + t
  let D := B - 11 / 39
  let d := A - Real.sqrt (2 * H)
  let d₀ := 11 / 39 - Real.sqrt (radicand B)
  let a := t - gamma
  let w := 1 - B
  have ht0 : 0 < t := by linarith only [ht]
  have hB : B ∈ Set.Icc (112 / 351 : ℝ) (1 / 3) := by
    dsimp [B]
    constructor <;> linarith only [hA, ht, hmass]
  have hD : 0 < D := by dsimp [D]; linarith only [hB.1]
  have htD : t ≤ D := by dsimp [D, B]; linarith only [hA]
  have hw : 0 ≤ w := by dsimp [w]; linarith only [hB.2]
  have ha : 0 < a := sub_pos.mpr hgt
  have hag : a ≤ gamma := by dsimp [a]; linarith only [htg]
  have hg0 : 0 < gamma := by linarith only [hgamma]
  have hL0 : 0 < L := (mul_pos (by norm_num) hv).trans_le hL
  have hrad : 0 ≤ radicand B := by dsimp [radicand, B]; linarith only [hH, hHcap]
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (radicand B)
  have hd₀ : 0 < d₀ := by
    dsimp [d₀, radicand]
    dsimp [radicand] at hs hs0
    nlinarith only [hs, hs0, hB.1]
  have hroot : Real.sqrt (2 * H) ≤ Real.sqrt (radicand B) := by
    apply Real.sqrt_le_sqrt
    dsimp [radicand, B]
    linarith only [hHcap]
  have hdd : d₀ ≤ d := by dsimp [d₀, d]; linarith only [hroot, hA]
  have hd : 0 < d := hd₀.trans_le hdd
  have hfirst : 0 ≤ a * L - d * X := by
    dsimp [a, d]
    linarith only [hcopy]
  have hsecond : 0 ≤ gamma ^ 2 * L - a * d * X := by
    have hp := mul_nonneg ha.le hfirst
    have hg := mul_le_mul hag hag ha.le hg0.le
    have hs := mul_nonneg (sub_nonneg.mpr hg) hL0.le
    nlinarith only [hp, hs]
  have hproduct := mul_nonneg hfirst hsecond
  have hmixed' : (d * X + gamma * L) ^ 2 ≤ 2 * v * V * X := hmixed
  have hscaled := mul_le_mul_of_nonneg_right hmixed' ha.le
  have hraw : d * t ^ 2 * L ≤ 2 * v * V * a := by
    apply (mul_le_mul_iff_left₀ hX).mp
    dsimp [a] at hproduct hscaled ⊢
    nlinarith only [hproduct, hscaled]
  have hpaid : d * t * L ≤ 2 * v * w * a := by
    apply (mul_le_mul_iff_left₀ ht0).mp
    calc
      (d * t * L) * t = d * t ^ 2 * L := by ring
      _ ≤ 2 * v * V * a := hraw
      _ ≤ 2 * v * (t * w) * a := by
        have hV : V ≤ t * w := by
          convert hVcap using 1
          dsimp [w, B]
          ring
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hV (by positivity)) ha.le
      _ = (2 * v * w * a) * t := by ring
  have hratio : a * D ≤ (D - 1 / 27) * t := by
    have hp := mul_nonneg (sub_nonneg.mpr hgamma) hD.le
    dsimp [a] at *
    nlinarith only [hp, htD]
  have hpaid₀ : d₀ * D * L ≤ 2 * v * w * (D - 1 / 27) := by
    apply (mul_le_mul_iff_left₀ ht0).mp
    calc
      (d₀ * D * L) * t ≤ (d * D * L) * t := by gcongr
      _ = (d * t * L) * D := by ring
      _ ≤ (2 * v * w * a) * D := mul_le_mul_of_nonneg_right hpaid hD.le
      _ = (2 * v * w) * (a * D) := by ring
      _ ≤ (2 * v * w) * ((D - 1 / 27) * t) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (2 * v * w * (D - 1 / 27)) * t := by ring
  have hlim := limiting_ratio_lt hB hrad
  change 2 * w * (D - 1 / 27) / (D * d₀) < 439 / 315 at hlim
  have hlim' := (div_lt_iff₀ (mul_pos hD hd₀)).mp hlim
  have hstrict := mul_lt_mul_of_pos_right hlim' hv
  have hlower := mul_le_mul_of_nonneg_left hL (mul_nonneg hd₀.le hD.le)
  nlinarith only [hpaid₀, hstrict, hlower]

end Erdos1017.CuspThreeDispersionScalar
