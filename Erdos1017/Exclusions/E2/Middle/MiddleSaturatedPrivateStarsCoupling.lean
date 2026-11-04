module

public import Erdos1017.Exclusions.E2.Middle.MiddleSaturatedPrivateStarsAlgebra

/-!
# Coupled reduction of the five star margins

The product-coupled surplus reduction to the canonical signed-price point works
simultaneously for all five scalar endpoint margins
(`all_margins_ge_canonical`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleSaturatedPrivateStarsCoupling

open MiddleSaturatedPrivateStarsAlgebra

private theorem affine_margin_coupling (u z L L0 v a b : ℝ)
    (hu : z ≤ u) (hL : L - L0 ≤ 2 * v / 3 * (u - z))
    (hb : 0 ≤ b) (ha : 2 * v / 3 * b ≤ a) :
    a * z - b * L0 ≤ a * u - b * L := by
  have h1 := mul_le_mul_of_nonneg_left hL hb
  have h2 := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hu)
  nlinarith only [h1, h2]

private theorem coupling_data (u v p tau L : ℝ) (hu : 0 < u)
    (hvtau : v ≤ tau) (htau : 0 < tau) (hp : p < u * v)
    (hL : L ≤ 2 * (u * v - p) / 3) :
    let z := max p 0 / tau
    let L0 := max (-2 * p) 0 / 3
    z ≤ u ∧ L - L0 ≤ 2 * v / 3 * (u - z) := by
  by_cases hp0 : 0 ≤ p
  · have hz : max p 0 = p := max_eq_left hp0
    have hl0 : max (-2 * p) 0 = 0 := max_eq_right (by linarith)
    simp only [hz, hl0, zero_div, sub_zero]
    have hutau : p ≤ u * tau := by
      have h := mul_le_mul_of_nonneg_left hvtau hu.le
      nlinarith only [hp, h]
    have hzu : p / tau ≤ u := (div_le_iff₀ htau).mpr (by nlinarith only [hutau])
    have hvp : v * (p / tau) ≤ p := by
      calc
        v * (p / tau) = v * p / tau := by ring
        _ ≤ p := (div_le_iff₀ htau).mpr (by
          nlinarith only [mul_le_mul_of_nonneg_right hvtau hp0])
    exact ⟨hzu, by nlinarith only [hL, hvp]⟩
  · have hpn : p < 0 := lt_of_not_ge hp0
    have hz : max p 0 = 0 := max_eq_right hpn.le
    have hl0 : max (-2 * p) 0 = -2 * p := max_eq_left (by linarith)
    simp only [hz, hl0, zero_div]
    exact ⟨hu.le, by nlinarith only [hL]⟩

/-- Product-coupled surplus reduction to the canonical signed-price point
works simultaneously for all five actual scalar endpoint margins. -/
theorem all_margins_ge_canonical (A ell g tau u v p L : ℝ)
    (hA : 0 < A) (hu : 0 < u) (hv : 0 < v) (hvA : v < A)
    (hvtau : v ≤ tau) (htau : 0 < tau)
    (hell : ell ∈ Icc (9 / 11 : ℝ) 1) (hg : 0 < g)
    (hp : p < u * v) (hL : L ≤ 2 * (u * v - p) / 3) :
    let z := max p 0 / tau
    let L0 := max (-2 * p) 0 / 3
    firstMargin A ell g tau z L0 ≤ firstMargin A ell g tau u L ∧
    secondMargin A ell g tau z L0 ≤ secondMargin A ell g tau u L ∧
    thirdMargin A ell g tau z L0 ≤ thirdMargin A ell g tau u L ∧
    fourthMargin A ell g tau z L0 ≤ fourthMargin A ell g tau u L ∧
    fifthMargin A ell g tau z L0 ≤ fifthMargin A ell g tau u L := by
  let z : ℝ := max p 0 / tau
  let L0 : ℝ := max (-2 * p) 0 / 3
  obtain ⟨hzu, hcouple⟩ := coupling_data u v p tau L hu hvtau htau hp hL
  have he0 : 0 ≤ ell := by linarith only [hell.1]
  have hd0 : 0 ≤ 1 - ell / 2 := by linarith only [hell.2]
  have hcoef1 : 2 * v / 3 ≤ A := by linarith only [hvA, hv]
  have hcoef2 : 2 * v / 3 ≤ g + ell * tau := by
    have h1 := mul_nonneg (show 0 ≤ ell - 2 / 3 by linarith only [hell.1]) htau.le
    have h2 := mul_nonneg (show (0 : ℝ) ≤ 2 / 3 by norm_num)
      (sub_nonneg.mpr hvtau)
    nlinarith only [h1, h2, hg]
  have hcoef3 : 2 * v / 3 * (1 - ell / 2) ≤ 3 * A * ell / 2 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hvA.le) he0
    have h2 := mul_nonneg hv.le (show 0 ≤ 11 * ell - 4 by linarith only [hell.1])
    nlinarith only [h1, h2]
  have hcoef4 : 2 * v / 3 * (1 - ell / 2) ≤
      g + ell * tau + ell * A / 2 := by
    have h1 := mul_nonneg he0 hA.le
    have h2 := mul_nonneg (show 0 ≤ ell / 2 by linarith only [he0]) hv.le
    nlinarith only [hcoef2, h1, h2, hell.2]
  have hcoef5 : 2 * v / 3 ≤ A * ell := by
    have h1 := mul_nonneg (sub_nonneg.mpr hvA.le) he0
    have h2 := mul_nonneg hv.le (show 0 ≤ ell - 2 / 3 by linarith only [hell.1])
    nlinarith only [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := affine_margin_coupling u z L L0 v A 1 hzu hcouple
      (by norm_num) (by nlinarith only [hcoef1])
    dsimp only [firstMargin]
    dsimp only [z, L0] at h
    nlinarith only [h]
  · have h := affine_margin_coupling u z L L0 v (g + ell * tau) 1
      hzu hcouple (by norm_num) (by nlinarith only [hcoef2])
    dsimp only [secondMargin]
    dsimp only [z, L0] at h
    nlinarith only [h]
  · have h := affine_margin_coupling u z L L0 v (3 * A * ell / 2)
      (1 - ell / 2) hzu hcouple hd0 hcoef3
    dsimp only [thirdMargin]
    dsimp only [z, L0] at h
    nlinarith only [h]
  · have h := affine_margin_coupling u z L L0 v
      (g + ell * tau + ell * A / 2) (1 - ell / 2) hzu hcouple hd0 hcoef4
    dsimp only [fourthMargin]
    dsimp only [z, L0] at h
    nlinarith only [h]
  · have h := affine_margin_coupling u z L L0 v (A * ell) 1
      hzu hcouple (by norm_num) (by simpa only [mul_one] using hcoef5)
    dsimp only [fifthMargin]
    dsimp only [z, L0] at h
    nlinarith only [h]

end Erdos1017.MiddleSaturatedPrivateStarsCoupling
