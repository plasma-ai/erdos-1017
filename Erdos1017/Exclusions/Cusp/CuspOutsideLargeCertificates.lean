module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Negative excess for the large-count outside-peak gate

On the whole real domain of the large reciprocal-cusp outside-peak scalar gate,
the excess is strictly negative (`outside_large_excess_neg`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CuspOutsideLarge

private theorem gap_polynomial_pos {m : ℝ} (hm : 9 ≤ m) :
    0 < 361 * m * (m + 3) ^ 3 - 800 * (2 * m + 1) ^ 3 := by
  have hn : 0 ≤ m - 9 := sub_nonneg.mpr hm
  have hid : 361 * m * (m + 3) ^ 3 - 800 * (2 * m + 1) ^ 3 =
      127072 + 294576 * (m - 9) + 90516 * (m - 9) ^ 2 +
        9845 * (m - 9) ^ 3 + 361 * (m - 9) ^ 4 := by ring
  rw [hid]
  positivity

private theorem radical_gap {m : ℝ} (hm : 9 ≤ m) :
    m / 2 < (19 / 20 : ℝ) * (m * (m + 3) / (2 * (2 * m + 1))) *
      Real.sqrt (m * (m + 3) / (2 * (2 * m + 1))) := by
  let B := m * (m + 3) / (2 * (2 * m + 1))
  have hm0 : 0 < m := by linarith
  have hden : 0 < 2 * m + 1 := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hb2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  have hgap : 0 < m ^ 2 * (361 * m * (m + 3) ^ 3 - 800 * (2 * m + 1) ^ 3) /
      (3200 * (2 * m + 1) ^ 3) := by
    exact div_pos (mul_pos (sq_pos_of_pos hm0) (gap_polynomial_pos hm)) (by positivity)
  have hid : ((19 / 20 : ℝ) * B * Real.sqrt B) ^ 2 - (m / 2) ^ 2 =
      m ^ 2 * (361 * m * (m + 3) ^ 3 - 800 * (2 * m + 1) ^ 3) /
        (3200 * (2 * m + 1) ^ 3) := by
    rw [mul_pow, mul_pow, hb2]
    dsimp [B]
    field_simp [hden.ne']
    ring
  have hnonneg : 0 ≤ (19 / 20 : ℝ) * B * Real.sqrt B := by positivity
  change m / 2 < (19 / 20 : ℝ) * B * Real.sqrt B
  nlinarith

private theorem cubic_monotone {x b D : ℝ} (hb : 3 / 2 ≤ b)
    (hx : b ≤ x) (hD : D ≤ 2) :
    (19 / 20 : ℝ) * b ^ 3 - D * b ^ 2 ≤ (19 / 20) * x ^ 3 - D * x ^ 2 := by
  have hxb : 0 ≤ x + b := by linarith
  have hcore : 0 ≤ (19 / 20 : ℝ) * (x ^ 2 + x * b + b ^ 2) - D * (x + b) := by
    have hfirst := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x + b / 2 by linarith)
    have hsecond := mul_nonneg (show 0 ≤ 57 * b / 40 - D by linarith) hxb
    nlinarith
  have hproduct := mul_nonneg (sub_nonneg.mpr hx) hcore
  nlinarith

/-- The complete real domain of the large reciprocal-cusp outside-peak
scalar gate has strictly negative excess. Physical reserve, slope and
split-envelope inequalities must supply the displayed scalar hypotheses. -/
theorem outside_large_excess_neg {m D x : ℝ} (hm : 9 ≤ m)
    (hD : D ≤ (2 * m + 1) / (m + 1)) (hx : 0 ≤ x)
    (hB : m * (m + 3) / (2 * (2 * m + 1)) ≤ x ^ 2) :
    x ^ 2 * (D - 19 * x / 20) < D - 1 := by
  let B := m * (m + 3) / (2 * (2 * m + 1))
  have hm1 : 0 < m + 1 := by linarith
  have hden : 0 < 2 * m + 1 := by linarith
  have hbase : (54 / 19 : ℝ) ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ (show 0 < 2 * (2 * m + 1) by positivity)).mpr
    have hproduct := mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ 19 * m + 12 by linarith)
    nlinarith
  have hB0 : 0 ≤ B := by linarith
  have hb : (3 / 2 : ℝ) ≤ Real.sqrt B :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hbx : Real.sqrt B ≤ x := Real.sqrt_le_iff.mpr ⟨hx, hB⟩
  have hDup : (2 * m + 1) / (m + 1) ≤ 2 := by
    apply (div_le_iff₀ hm1).mpr
    linarith
  have hmono := cubic_monotone hb hbx (hD.trans hDup)
  have hb2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  have hb3 : Real.sqrt B ^ 3 = B * Real.sqrt B := by rw [pow_succ, hb2]
  rw [hb3, hb2] at hmono
  have hid : (2 * m + 1) / (m + 1) * (B - 1) + 1 = m / 2 := by
    dsimp [B]
    field_simp [hm1.ne', hden.ne']
    ring
  have hupper : D * (B - 1) + 1 ≤ m / 2 := by
    have hproduct := mul_le_mul_of_nonneg_right hD (show 0 ≤ B - 1 by linarith)
    linarith
  have hrad : m / 2 < (19 / 20 : ℝ) * B * Real.sqrt B := radical_gap hm
  nlinarith

end Erdos1017.CuspOutsideLarge
