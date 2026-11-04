module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Closing scalar contradiction for the saturated private case

The saturated score cap `δ - 2g = 9q²/((q+2)R(q)) < 7/100` holds on `(0, 1/5]`,
and the score lower bound `A(1-κ) + kκ ≤ Δ`, the flat saturated-head row and the
own-multiplier and gap guards combine into the final private saturated
contradiction (`saturated_private_false`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleSaturatedPrivateScalar

open LowerE2Scalar

/-- The saturated score cap `δ - 2g = 9q²/((q+2)R(q)) < 7/100` on `(0, 1/5]`. -/
theorem score_cap {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (1 / 5)) :
    1 - multiplier q - 2 * gapFloor q < 7 / 100 := by
  have hq0 := hq.1
  have hR := denominator_pos hq0.le
  have hq2 : 0 < 2 + q := by linarith
  have hP : 0 < (2 + q) * denominator q := mul_pos hq2 hR
  have hid : (1 - multiplier q - 2 * gapFloor q) * ((2 + q) * denominator q) = 9 * q ^ 2 := by
    unfold multiplier gapFloor
    field_simp
    unfold denominator
    ring
  by_contra h
  push_neg at h
  have h1 := mul_le_mul_of_nonneg_right h hP.le
  rw [hid] at h1
  unfold denominator at h1
  nlinarith [mul_nonneg hq0.le (sub_nonneg.mpr hq.2), pow_nonneg hq0.le 3]

/-- The final private saturated scalar contradiction. The inputs are the
score lower bound `A(1-κ) + kκ ≤ Δ`, the flat saturated-head row, the
own-multiplier and gap guards, and the curvature consequence
`ℓ < 2Ck(A+k)` with `ℓ = -m`. -/
theorem saturated_private_false {A b k n κ m ν g C : ℝ}
    (hA : 1 / 4 < A) (hA3 : A ≤ 1 / 3) (hb : 0 ≤ b) (hk : 0 < k)
    (hn : n = 1 - A - b - k) (hm1 : -1 < m) (hm2 : m < -(9 / 11))
    (hgν : g < ν + m) (hrow : ν ≤ (1 - m) * n) (hrm : 19 / 40 * (1 - m) < g - m)
    (hcap : 1 + m - 2 * g < 7 / 100)
    (hmκ : m ≤ κ) (hκ1 : κ < 1)
    (hscore : A * (1 - κ) + k * κ ≤ 1 - m - 2 * ν)
    (hC : 0 < C) (hC6 : C < 6) (hcurv : -m < 2 * C * k * (A + k)) : False := by
  have hΔ : 1 - m - 2 * ν < 7 / 100 := by linarith
  have hn1 : 19 / 40 < n := by
    by_contra h
    have h1 := mul_le_mul_of_nonneg_left (le_of_not_gt h) (show 0 ≤ 1 - m by linarith)
    linarith
  have hk7 : k < 7 / 100 := by
    by_contra hk7
    push_neg at hk7
    by_cases hκ0 : 0 ≤ κ
    · have h1 : 7 / 100 * (1 - κ) ≤ A * (1 - κ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h2 : 7 / 100 * κ ≤ k * κ := mul_le_mul_of_nonneg_right hk7 hκ0
      linarith
    · have hAk : -(1 / 40) < A - k := by linarith
      have h3 : (-κ) * (-(1 / 40)) ≤ (-κ) * (A - k) :=
        mul_le_mul_of_nonneg_left hAk.le (by linarith)
      linarith
  have hAk : A + k < 1 / 3 + 7 / 100 := by linarith
  have hkA : k * (A + k) < 7 / 100 * (1 / 3 + 7 / 100) :=
    mul_lt_mul'' hk7 hAk hk.le (by linarith)
  have hCkA : C * (k * (A + k)) < 6 * (7 / 100 * (1 / 3 + 7 / 100)) :=
    mul_lt_mul'' hC6 hkA hC.le (by positivity)
  have heq : 2 * C * k * (A + k) = 2 * (C * (k * (A + k))) := by ring
  linarith

end Erdos1017.MiddleSaturatedPrivateScalar
