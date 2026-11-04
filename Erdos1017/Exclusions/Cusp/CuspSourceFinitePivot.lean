module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite mass shift with the radical trace price

A finite mass shift exists with exact density return and the radical trace price
(`exists_shift`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CuspSourceFinitePivot

/-- A finite mass shift with exact density return and the radical trace price. -/
theorem exists_shift {A z g κ : ℝ} (hA : 0 < A) (hz : 0 < z)
    (hg : g ∈ Set.Icc (0 : ℝ) 1) (hκ : 0 ≤ κ) (hD : 0 < A - (1 - g) * z) :
    ∃ x y : ℝ, 0 < y ∧ -A ≤ x ∧ x ≤ 0 ∧ x + y ≤ 0 ∧
      (z + κ) * x + (A + g * z + κ) * y + x * y + g * y ^ 2 / 2 = 0 ∧
      -z * x / y ≤ (z + Real.sqrt (z ^ 2 + 2 * A * z)) / 2 := by
  have hg0 := hg.1
  have hg1 := hg.2
  let w := Real.sqrt (z ^ 2 + 2 * A * z) - z
  have hs := Real.sq_sqrt (show 0 ≤ z ^ 2 + 2 * A * z by positivity)
  have hsn := Real.sqrt_nonneg (z ^ 2 + 2 * A * z)
  have hw : 0 < w := by dsimp [w]; nlinarith [mul_pos hA hz]
  have hwEq : w ^ 2 + 2 * z * w = 2 * A * z := by dsimp [w]; nlinarith
  let D := A - (1 - g) * z
  let y := min D w
  have hy : 0 < y := lt_min hD hw
  have hyD : y ≤ D := min_le_left _ _
  have hyw : y ≤ w := min_le_right _ _
  have hDA : D ≤ A := by dsimp [D]; nlinarith [mul_nonneg (sub_nonneg.mpr hg.2) hz.le]
  have hyA : y ≤ A := hyD.trans hDA
  have hyQuad : y ^ 2 + 2 * z * y ≤ 2 * A * z := by
    nlinarith [sq_le_sq₀ hy.le hw.le |>.2 hyw]
  let den := z + κ + y
  have hden : 0 < den := by dsimp [den]; positivity
  let x := -y * (A + g * z + κ + g * y / 2) / den
  have hx : x * den = -y * (A + g * z + κ + g * y / 2) := by
    dsimp [x]
    exact div_mul_cancel₀ _ hden.ne'
  have hx0 : x ≤ 0 := by
    dsimp [x]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy.le) (by positivity)) hden.le
  have hxA : -A ≤ x := by
    apply (mul_le_mul_iff_left₀ hden).mp
    rw [hx]
    have hgy : g * (y ^ 2 + 2 * z * y) ≤ y ^ 2 + 2 * z * y :=
      mul_le_of_le_one_left (by positivity) hg.2
    have hκy := mul_le_mul_of_nonneg_left hyA hκ
    dsimp [den]
    nlinarith
  have hxy : x + y ≤ 0 := by
    apply (mul_le_mul_iff_left₀ hden).mp
    rw [add_mul, hx, zero_mul]
    have hDy : 0 ≤ y * (D - y) := mul_nonneg hy.le (sub_nonneg.mpr hyD)
    dsimp [den, D] at *
    nlinarith [mul_nonneg hg.1 (sq_nonneg y)]
  have hdensity : (z + κ) * x + (A + g * z + κ) * y + x * y +
      g * y ^ 2 / 2 = 0 := by
    dsimp [den] at hx
    nlinarith
  have hprice : -z * x / y ≤ z + w / 2 := by
    apply (div_le_iff₀ hy).2
    apply (mul_le_mul_iff_left₀ hden).mp
    have hxz : (-z * x) * den =
        z * y * (A + g * z + κ + g * y / 2) := by
      calc
        _ = -z * (x * den) := by ring
        _ = _ := by rw [hx]; ring
    rw [hxz]
    have hbase : z * (A + g * z + κ + g * y / 2) ≤ (z + w / 2) * den := by
      by_cases hDw : D ≤ w
      · have hyEq : y = D := min_eq_left hDw
        have hgap : 0 ≤ (1 - g) * z * D := by positivity
        have hκD : 0 ≤ κ * D := mul_nonneg hκ hD.le
        have hκw : 0 ≤ κ * w := mul_nonneg hκ hw.le
        have hDwz : z * D ≤ z * w := mul_le_mul_of_nonneg_left hDw hz.le
        have hDwD : D ^ 2 ≤ D * w := by nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hDw)]
        dsimp [den]
        rw [hyEq]
        dsimp [D] at *
        nlinarith
      · have hyEq : y = w := min_eq_right (le_of_not_ge hDw)
        have hgterm : 0 ≤ (1 - g) * z * (2 * z + w) := by positivity
        have hκw : 0 ≤ κ * w := mul_nonneg hκ hw.le
        dsimp [den]
        rw [hyEq]
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hbase hy.le]
  refine ⟨x, y, hy, hxA, hx0, hxy, hdensity, ?_⟩
  dsimp [w] at hprice
  linarith

end Erdos1017.CuspSourceFinitePivot
