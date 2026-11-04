module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Whole-source child payment at counts at least six

At reciprocal count `k ≥ 6`, a peak inside the entire source is impossible: one
shared source budget pays the whole-source child at both ends of the
outside-square interval, and the child cost and signed score contradict that
budget (`source_peak_false`). The strict slope bracket supplies the normalized
constants.
-/

@[expose] public section

namespace Erdos1017.CuspSourcePeakPayment

/-- One shared source budget pays the whole-source child at both ends of the
actual outside-square interval. `D * LZ ≤ N * BUD + D * X` spends `BUD` once;
`X` is a separately bounded excess. -/
theorem child_payment {δ ell a T r z QO e V BUD LZ child N D X : ℝ}
    (hz : 0 < z) (hD : 0 < D) (hN : 0 ≤ N) (hell : 1 < ell)
    (he : 0 < e) (hV : 0 ≤ V) (hBUD : 0 ≤ BUD) (hQO : 0 ≤ QO) (hT : T = 2 * r)
    (hscore : z * (child - r ^ 2) =
      z * (e + V / 2 + δ * a ^ 2 / 2 + ell * QO / 2 + (ell - 1) * T ^ 2 / 4) - LZ)
    (hbudget : e + V / 2 + BUD + (ell - 1) * QO / 2 ≤ δ * (T ^ 2 - a ^ 2) / 2)
    (hloss : D * LZ ≤ N * BUD + D * X)
    (hzero : N * (δ * (T ^ 2 - a ^ 2) / 2) + D * X ≤
      D * z * (δ * a ^ 2 / 2 + (ell - 1) * T ^ 2 / 4))
    (hfull : (2 - ell) * (δ * (T ^ 2 - a ^ 2) / 2) * z + (ell - 1) * X ≤
      (ell - 1) * z * (δ * a ^ 2 / 2 + ell * T ^ 2 / 4)) :
    max (r ^ 2) QO < child := by
  have hDz : 0 < D * z := mul_pos hD hz
  have hgain : 0 < (D * z + N) * (e + V / 2) := mul_pos (by linarith) (by linarith)
  have hB : 0 ≤ δ * (T ^ 2 - a ^ 2) / 2 - (ell - 1) * QO / 2 := by linarith
  have hspent : N * BUD ≤ N * (δ * (T ^ 2 - a ^ 2) / 2 - (ell - 1) * QO / 2 - e - V / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hN
  have hvalue : D * (z * (child - r ^ 2)) = D * (z * (e + V / 2 + δ * a ^ 2 / 2 +
      ell * QO / 2 + (ell - 1) * T ^ 2 / 4) - LZ) := by
    rw [hscore]
  have hhalf : D * z * r ^ 2 = D * z * T ^ 2 / 4 := by
    rw [hT]
    ring
  have hrise : 0 ≤ D * z * ell * QO := mul_nonneg (mul_nonneg hDz.le (by linarith)) hQO
  have hrest : 0 ≤ N * (ell - 1) * QO := mul_nonneg (mul_nonneg hN (by linarith)) hQO
  have hlow : r ^ 2 < child := by
    have hpos : 0 < D * z * (child - r ^ 2) := by linarith
    exact sub_pos.mp (pos_of_mul_pos_right hpos hDz.le)
  have hgap : 0 ≤ D * z * (δ * a ^ 2 / 2 + ell * QO / 2 + (ell - 1) * T ^ 2 / 4 +
      T ^ 2 / 4 - QO) - N * (δ * (T ^ 2 - a ^ 2) / 2 - (ell - 1) * QO / 2) - D * X := by
    rcases le_total ((2 - ell) * (D * z)) (N * (ell - 1)) with hslope | hslope
    · have hup := mul_nonneg hQO (sub_nonneg.mpr hslope)
      have hT2 := mul_nonneg hDz.le (sq_nonneg T)
      linarith
    · have hweight := mul_nonneg hB (sub_nonneg.mpr hslope)
      have hcheck := mul_nonneg hD.le (sub_nonneg.mpr hfull)
      refine le_of_not_gt fun hneg => ?_
      have hscaled := mul_neg_of_pos_of_neg (sub_pos.mpr hell) hneg
      linarith
  have hhigh : QO < child := by
    have hpos : 0 < D * z * (child - QO) := by linarith
    exact sub_pos.mp (pos_of_mul_pos_right hpos hDz.le)
  exact max_lt hlow hhigh

set_option maxHeartbeats 600000 in
/-- Reciprocal count `k ≥ 6`, original peak inside the entire source: the
actual whole-source child cost and signed score contradict the one shared
source budget. Resource signs, the restricted trace cap and the original
reserve consequences are explicit. -/
theorem source_peak_false {a ell e V E b A z r cI CJ Phi FJ QO child : ℝ}
    (ha : a ≤ 1 / 6) (hell : 29 / 21 ≤ ell) (hdelta : 0 ≤ 2 - 2 * a - ell)
    (hrho : 4 * (2 - 2 * a - ell) ≤ 3 * (ell - 1))
    (he : 0 < e) (hV : 0 ≤ V) (hb : 0 ≤ b) (hA : 0 < A) (hz : 0 < z)
    (hcI : 0 ≤ cI) (hCJ : 0 ≤ CJ) (hPhi : 0 ≤ Phi) (hFJ : 0 ≤ FJ) (hQO : 0 ≤ QO)
    (hr : r = (b + A + z) / 2) (htwo : b + A + z ≤ 2 * a)
    (hsquare : (A + b) ^ 2 ≤ a ^ 2) (hhead : b ≤ A)
    (hreserve : (2 - 2 * a - ell) * a ^ 2 ≤ (2 - ell) * A ^ 2)
    (htrace : FJ ≤ (ell + 1 / 50) * z ^ 2)
    (hE : E = 2 * (A * Phi) + FJ + V + 2 * (A * cI + CJ))
    (hbudget : e + E / 2 + (ell - 1) * QO / 2 ≤
      (2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2)
    (hcost : child ≤ max (r ^ 2) QO)
    (hscore : child - r ^ 2 =
      e + (2 - 2 * a - ell) * a ^ 2 / 2 + ell * QO / 2 + V / 2 +
        (ell - 1) * (b + A + z) ^ 2 / 4 - (r - A) * cI - ((r - z) / z) * CJ +
        ((r - A) * (r - z) / z) * Phi - (A + b) * FJ / (2 * z)) :
    False := by
  subst hr
  have hT : 0 < b + A + z := by linarith
  have hell1 : 1 < ell := by linarith
  have hT2 : (b + A + z) ^ 2 ≤ 4 * a ^ 2 := by
    nlinarith [mul_le_mul htwo htwo hT.le (by linarith : (0 : ℝ) ≤ 2 * a)]
  have hBUD : 0 ≤ A * cI + CJ + A * Phi + FJ / 2 := by
    have hI := mul_nonneg hA.le hcI
    have hP := mul_nonneg hA.le hPhi
    linarith
  have hspent : e + V / 2 + (A * cI + CJ + A * Phi + FJ / 2) + (ell - 1) * QO / 2 ≤
      (2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2 := by
    rw [hE] at hbudget
    linarith
  have hz0 : z ≠ 0 := hz.ne'
  have hzscore : z * (child - ((b + A + z) / 2) ^ 2) =
      z * (e + V / 2 + (2 - 2 * a - ell) * a ^ 2 / 2 + ell * QO / 2 +
        (ell - 1) * (b + A + z) ^ 2 / 4) -
      (z * ((b + A + z) / 2 - A) * cI + ((b + A + z) / 2 - z) * CJ -
        ((b + A + z) / 2 - A) * ((b + A + z) / 2 - z) * Phi + (A + b) * FJ / 2) := by
    rw [hscore]
    field_simp
    ring
  have hfull : (2 - ell) * ((2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2) * z +
      (ell - 1) * 0 ≤
      (ell - 1) * z * ((2 - 2 * a - ell) * a ^ 2 / 2 + ell * (b + A + z) ^ 2 / 4) := by
    have q1 := mul_nonneg hz.le
      (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 4 * a ^ 2 - (b + A + z) ^ 2))
    have q2 := mul_nonneg (mul_nonneg hz.le (sq_nonneg (b + A + z)))
      (mul_nonneg (by linarith : (0 : ℝ) ≤ ell)
        (by linarith : (0 : ℝ) ≤ 3 * (ell - 1) - 4 * (2 - 2 * a - ell)))
    have q3 := mul_nonneg (mul_nonneg hz.le (sq_nonneg (b + A + z)))
      (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 20 * ell - 21))
    linarith only [q1, q2, q3]
  rcases le_total (3 * z) (b + A + z) with hsmall | hlarge
  · have hzA : z ≤ A := by linarith
    have hhalf : 0 ≤ (b + A + z) / 2 := by linarith
    have hloss : 1 * (z * ((b + A + z) / 2 - A) * cI + ((b + A + z) / 2 - z) * CJ -
        ((b + A + z) / 2 - A) * ((b + A + z) / 2 - z) * Phi + (A + b) * FJ / 2) ≤
        ((b + A + z) / 2 - z) * (A * cI + CJ + A * Phi + FJ / 2) +
          1 * ((b + A + z) / 2 * (ell + 1 / 50) * z ^ 2 / 2) := by
      have h1 := mul_nonneg (mul_nonneg hhalf (sub_nonneg.mpr hzA)) hcI
      have h2 := mul_nonneg
        (mul_nonneg hhalf (by linarith : (0 : ℝ) ≤ (b + A + z) / 2 - z)) hPhi
      have h3 := mul_le_mul_of_nonneg_left htrace hhalf
      linarith only [h1, h2, h3]
    have hzero : ((b + A + z) / 2 - z) *
          ((2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2) +
        1 * ((b + A + z) / 2 * (ell + 1 / 50) * z ^ 2 / 2) ≤
        1 * z * ((2 - 2 * a - ell) * a ^ 2 / 2 + (ell - 1) * (b + A + z) ^ 2 / 4) := by
      have p1 := mul_nonneg hT.le (mul_nonneg hdelta (sub_nonneg.mpr hsquare))
      have p2 := mul_nonneg (mul_nonneg hT.le hz.le)
        (mul_nonneg (by linarith : (0 : ℝ) ≤ ell - 1)
          (by linarith : (0 : ℝ) ≤ b + A + z - 3 * z))
      have p3 := mul_nonneg (mul_nonneg (mul_nonneg hT.le hz.le) hz.le)
        (by linarith : (0 : ℝ) ≤ ell - 1 - 2 * a - 1 / 50)
      linarith only [p1, p2, p3]
    have htraceFull :
        (2 - ell) * ((2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2) * z +
          (ell - 1) * ((b + A + z) / 2 * (ell + 1 / 50) * z ^ 2 / 2) ≤
        (ell - 1) * z * ((2 - 2 * a - ell) * a ^ 2 / 2 + ell * (b + A + z) ^ 2 / 4) := by
      have q1 := mul_nonneg hz.le
        (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 4 * a ^ 2 - (b + A + z) ^ 2))
      have q2 := mul_nonneg (mul_nonneg hz.le (sq_nonneg (b + A + z)))
        (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (ell - 1) - 4 * (2 - 2 * a - ell))
          (by linarith : (0 : ℝ) ≤ 100 * ell - 1))
      have q3 := mul_nonneg (mul_nonneg hz.le (sq_nonneg (b + A + z)))
        (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 1300 * ell - 1579))
      have q4 := mul_nonneg
        (mul_nonneg (mul_nonneg hz.le (by linarith : (0 : ℝ) ≤ ell - 1))
          (by linarith : (0 : ℝ) ≤ ell + 1 / 50))
        (mul_nonneg hT.le (by linarith : (0 : ℝ) ≤ b + A + z - 3 * z))
      linarith only [q1, q2, q3, q4]
    exact not_le.mpr (child_payment (δ := 2 - 2 * a - ell) (T := b + A + z)
      (r := (b + A + z) / 2) (BUD := A * cI + CJ + A * Phi + FJ / 2)
      (N := (b + A + z) / 2 - z) (D := 1)
      (X := (b + A + z) / 2 * (ell + 1 / 50) * z ^ 2 / 2)
      hz one_pos (by linarith) hell1 he hV hBUD hQO (by ring) hzscore hspent
      hloss hzero htraceFull) hcost
  · rcases le_total (2 * A) z with hpeak | hpeak
    · have hhalf : 0 ≤ (b + A + z) / 2 := by linarith
      have hgapA : 0 ≤ (b + A + z) / 2 - A := by linarith
      have hloss : A * (z * ((b + A + z) / 2 - A) * cI + ((b + A + z) / 2 - z) * CJ -
          ((b + A + z) / 2 - A) * ((b + A + z) / 2 - z) * Phi + (A + b) * FJ / 2) ≤
          z * ((b + A + z) / 2 - A) * (A * cI + CJ + A * Phi + FJ / 2) + A * 0 := by
        have h1 := mul_nonneg (mul_nonneg hhalf (by linarith : (0 : ℝ) ≤ z - A)) hCJ
        have h2 := mul_nonneg (mul_nonneg (mul_nonneg hA.le hhalf) hgapA) hPhi
        have h3 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hpeak) hT.le) hFJ
        linarith only [h1, h2, h3]
      have hlin : 3 / 4 * (2 - 2 * a - ell) * (b + A + z) ≤
          (ell - 1 + 2 * (2 - 2 * a - ell)) * A := by
        have t1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hdelta) hdelta
        have t2 := mul_le_mul_of_nonneg_left hreserve hdelta
        have t3 := mul_nonneg (add_nonneg (sq_nonneg (ell - 1 - 2 * (2 - 2 * a - ell)))
          (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 41 / 4 * ell - 25 / 2))) (sq_nonneg A)
        have hR : 0 ≤ (ell - 1 + 2 * (2 - 2 * a - ell)) * A := mul_nonneg (by linarith) hA.le
        refine le_of_not_gt fun hlt => ?_
        have hgap := sub_pos.mpr hlt
        have hsq := mul_pos hgap hgap
        have hmix := mul_nonneg hgap.le hR
        linarith only [t1, t2, t3, hsq, hmix]
      have hzero : z * ((b + A + z) / 2 - A) *
            ((2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2) + A * 0 ≤
          A * z * ((2 - 2 * a - ell) * a ^ 2 / 2 + (ell - 1) * (b + A + z) ^ 2 / 4) := by
        have p1 := mul_nonneg (mul_nonneg hz.le hT.le)
          (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 4 * a ^ 2 - (b + A + z) ^ 2))
        have p2 := mul_nonneg (mul_nonneg (mul_nonneg hz.le hT.le) hT.le) (sub_nonneg.mpr hlin)
        linarith only [p1, p2]
      exact not_le.mpr (child_payment (δ := 2 - 2 * a - ell) (T := b + A + z)
        (r := (b + A + z) / 2) (BUD := A * cI + CJ + A * Phi + FJ / 2)
        (N := z * ((b + A + z) / 2 - A)) (D := A) (X := 0)
        hz hA (mul_nonneg hz.le hgapA) hell1 he hV hBUD hQO (by ring) hzscore hspent
        hloss hzero hfull) hcost
    · have hrate : z * ((b + A + z) / 2 - A) ≤ A * (A + b) := by
        have hw := mul_nonneg (sub_nonneg.mpr hpeak) hT.le
        linarith only [hw]
      have hcoef : 0 ≤ A * (A + b) + ((b + A + z) / 2 - A) * ((b + A + z) / 2 - z) := by
        have h1 := mul_nonneg hA.le hb
        have h2 := mul_nonneg (sub_nonneg.mpr hpeak) hz.le
        nlinarith only [h1, h2, sq_nonneg A, sq_nonneg b]
      have hloss : 1 * (z * ((b + A + z) / 2 - A) * cI + ((b + A + z) / 2 - z) * CJ -
          ((b + A + z) / 2 - A) * ((b + A + z) / 2 - z) * Phi + (A + b) * FJ / 2) ≤
          (A + b) * (A * cI + CJ + A * Phi + FJ / 2) + 1 * 0 := by
        have h1 := mul_nonneg (sub_nonneg.mpr hrate) hcI
        have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ (b + A + z) / 2) hCJ
        have h3 := mul_nonneg hcoef hPhi
        linarith only [h1, h2, h3]
      have hzero : (A + b) * ((2 - 2 * a - ell) * ((b + A + z) ^ 2 - a ^ 2) / 2) + 1 * 0 ≤
          1 * z * ((2 - 2 * a - ell) * a ^ 2 / 2 + (ell - 1) * (b + A + z) ^ 2 / 4) := by
        have p1 := mul_nonneg hT.le (mul_nonneg hdelta (sub_nonneg.mpr hsquare))
        have p2 := mul_nonneg (mul_nonneg (mul_nonneg hz.le hT.le) hT.le)
          (by linarith : (0 : ℝ) ≤ 3 * (ell - 1) - 4 * (2 - 2 * a - ell))
        have p3 := mul_nonneg (mul_nonneg hz.le hT.le)
          (mul_nonneg hdelta (by linarith : (0 : ℝ) ≤ 3 * z - (b + A + z)))
        linarith only [p1, p2, p3]
      exact not_le.mpr (child_payment (δ := 2 - 2 * a - ell) (T := b + A + z)
        (r := (b + A + z) / 2) (BUD := A * cI + CJ + A * Phi + FJ / 2)
        (N := A + b) (D := 1) (X := 0)
        hz one_pos (by linarith) hell1 he hV hBUD hQO (by ring) hzscore hspent
        hloss hzero hfull) hcost

/-- The strict reciprocal-cusp slope bracket at count `k ≥ 6` gives the
normalized constants of the source-peak payment. -/
theorem slope_constants {k : ℕ} (hk : 6 ≤ k) {ell : ℝ}
    (hell : ell ∈ Set.Ioo (2 - 2 / (k : ℝ) - 2 / ((k : ℝ) + 1)) (2 - 2 / (k : ℝ))) :
    1 / (k : ℝ) ≤ 1 / 6 ∧ 29 / 21 ≤ ell ∧ 0 ≤ 2 - 2 * (1 / (k : ℝ)) - ell ∧
      4 * (2 - 2 * (1 / (k : ℝ)) - ell) ≤ 3 * (ell - 1) := by
  have hk6 : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hu : 1 / (k : ℝ) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) hk6
  have hv : 1 / ((k : ℝ) + 1) ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2u : 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
  have h2v : 2 / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) := by ring
  rw [h2u, h2v] at hell
  exact ⟨hu, by linarith [hell.1], by linarith [hell.2], by linarith [hell.1]⟩

end Erdos1017.CuspSourcePeakPayment
