module

public import Erdos1017.Exclusions.Cusp.CuspSourcePeakPayment

/-!
# Payment for the fifth-cusp source peak

At the five-part reciprocal cusp, the whole-source child contradicts its cost
using one shared budget and the correlated trace (`source_peak_false`), after
the correlated and signed loss coefficients are paid by the missing-square
constraint and the zero-square endpoint price.
-/

@[expose] public section

namespace Erdos1017.CuspFiveSourcePeakPayment

/-- The correlated pair coefficient is paid by the original missing-square
constraint. The coefficient remains signed before applying the trace bound. -/
theorem correlated_coefficient {X t y : ℝ}
    (hX : 0 < X) (ht : 0 < t) (hsum : X + t ≤ 1)
    (hhead : 2 * (1 - t) / 3 ≤ X) (hy : 1 / 4 ≤ y) (hy1 : y < 1)
    (hsquare : (1 - t) ^ 2 ≤ y) :
    (X * (3 / 2 - 2 * t) + 3 * t / 2 - t ^ 2 - 1 / 4) * (1 - y) ≤
      t * (2 * X + t) * (y + 2 / 5) := by
  have ht1 : t < 1 := by linarith
  have hweight : 0 < t * (2 * X + t) := mul_pos ht (by linarith)
  let N := X * (3 / 2 - 2 * t) + 3 * t / 2 - t ^ 2 - 1 / 4
  rcases le_total t (1 / 2) with hsmall | hlarge
  · have hN : 0 ≤ N := by
      dsimp [N]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 2 - 2 * t)
        (by linarith : (0 : ℝ) ≤ X - 2 * (1 - t) / 3)]
    have hD : 0 ≤ 2 * X * (15 * t - 2) + 30 * t ^ 2 - 37 * t + 10 := by
      rcases le_total t (2 / 15) with hlow | hhigh
      · have hsub := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t - X)
          (by linarith : (0 : ℝ) ≤ 2 - 15 * t)
        nlinarith
      · have hsub := mul_nonneg (by linarith : (0 : ℝ) ≤ X - 2 * (1 - t) / 3)
          (by linarith : (0 : ℝ) ≤ 15 * t - 2)
        nlinarith [sq_nonneg (t - 43 / 60)]
    have hbase : N * (1 - (1 - t) ^ 2) ≤
        t * (2 * X + t) * ((1 - t) ^ 2 + 2 / 5) := by
      dsimp [N]
      nlinarith [mul_nonneg ht.le hD]
    have hchange := mul_nonneg (add_nonneg hN hweight.le) (sub_nonneg.mpr hsquare)
    dsimp [N] at *
    nlinarith only [hbase, hchange]
  · have hsub := mul_nonneg (by linarith : (0 : ℝ) ≤ X - 2 * (1 - t) / 3)
      (by linarith : (0 : ℝ) ≤ 56 * t / 15 - 3 / 2)
    have hpoly : 0 ≤ -112 * t ^ 2 + 358 * t - 135 := by
      have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 2)
        (by linarith : (0 : ℝ) ≤ 1 - t)
      nlinarith
    have hN : N ≤ 13 / 15 * (t * (2 * X + t)) := by
      dsimp [N]
      nlinarith only [hsub, hpoly]
    have hrest := mul_nonneg hweight.le (by linarith : (0 : ℝ) ≤ 28 * y - 7)
    have hscale := mul_le_mul_of_nonneg_right hN (by linarith : (0 : ℝ) ≤ 1 - y)
    dsimp [N] at *
    nlinarith only [hscale, hrest]

/-- All signed loss coefficients fit the zero-square endpoint price. The
original reserve is used only for the original-head coefficient. -/
theorem coefficient_bounds {rho X t y : ℝ}
    (hrho : 0 < rho) (hrho5 : rho ≤ 5 / 4) (hX : 0 < X) (ht : 0 < t)
    (hsum : X + t ≤ 1) (hhead : 2 * (1 - t) / 3 ≤ X)
    (hy : 1 / 4 ≤ y) (hy1 : y < 1) (hsquare : (1 - t) ^ 2 ≤ y)
    (hreserve : rho * y ≤ 11 / 4 * X ^ 2) :
    rho * (1 - y) * (1 / 2 - X) ≤ X * (rho * y + 1 / 2) ∧
    rho * (1 - y) * (1 / 2 - t) ≤ t * (rho * y + 1 / 2) ∧
    rho * (1 - y) *
        (X * (3 / 2 - 2 * t) + 3 * t / 2 - t ^ 2 - 1 / 4) ≤
      t * (2 * X + t) * (rho * y + 1 / 2) := by
  have hI : rho * (1 - y) * (1 / 2 - X) ≤ X * (rho * y + 1 / 2) := by
    rcases le_total (1 - y - 2 * X) 0 with hneg | hpos
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hrho.le hneg]
    · have hreserve' : rho ≤ 11 * X ^ 2 := by nlinarith
      have hscaled := mul_le_mul_of_nonneg_right hreserve' hpos
      have hpoly : 11 * X * (3 / 4 - 2 * X) ≤ 1 := by
        nlinarith [sq_nonneg (X - 3 / 16)]
      have hchange := mul_nonneg (sq_nonneg X) (by linarith : (0 : ℝ) ≤ y - 1 / 4)
      have hcheck := mul_le_mul_of_nonneg_left hpoly hX.le
      nlinarith only [hscaled, hchange, hcheck]
  have hJ : rho * (1 - y) * (1 / 2 - t) ≤ t * (rho * y + 1 / 2) := by
    have hbase : (1 - y) * (1 / 2 - t) ≤ t * (y + 2 / 5) := by
      nlinarith [sq_nonneg t]
    have hscaled := mul_le_mul_of_nonneg_left hbase hrho.le
    have hrest := mul_nonneg ht.le (by linarith : (0 : ℝ) ≤ 1 / 2 - 2 / 5 * rho)
    nlinarith only [hscaled, hrest]
  refine ⟨hI, hJ, ?_⟩
  have hbase := mul_le_mul_of_nonneg_left
    (correlated_coefficient hX ht hsum hhead hy hy1 hsquare) hrho.le
  have hrest := mul_nonneg (mul_nonneg ht.le (by linarith : (0 : ℝ) ≤ 2 * X + t))
    (by linarith : (0 : ℝ) ≤ 1 / 2 - 2 / 5 * rho)
  nlinarith only [hbase, hrest]

set_option maxHeartbeats 800000 in
/-- At the five-part reciprocal cusp, the literal whole-source child
contradicts its cost using one shared budget and the correlated trace. -/
theorem source_peak_false {ell e V E b A z r cI CJ Phi FJ QO child : ℝ}
    (hell : ell ∈ Set.Ioo (19 / 15) (8 / 5))
    (he : 0 < e) (hV : 0 ≤ V) (hb : 0 ≤ b) (hA : 0 < A) (hz : 0 < z)
    (hcI : 0 ≤ cI) (hCJ : 0 ≤ CJ) (hPhi : 0 ≤ Phi) (hFJ : 0 ≤ FJ) (hQO : 0 ≤ QO)
    (hr : r = (b + A + z) / 2)
    (hone : 1 / 5 < b + A + z) (htwo : b + A + z < 2 / 5)
    (hsquare : (A + b) ^ 2 ≤ (1 / 5 : ℝ) ^ 2) (hhead : b < A / 2)
    (hreserve : (8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 < (2 - ell) * A ^ 2)
    (htrace : FJ / 2 ≤ (A + z) * Phi)
    (hE : E = 2 * (A * Phi) + FJ + V + 2 * (A * cI + CJ))
    (hbudget : e + E / 2 + (ell - 1) * QO / 2 ≤
      (8 / 5 - ell) * ((b + A + z) ^ 2 - (1 / 5 : ℝ) ^ 2) / 2)
    (hcost : child ≤ max (r ^ 2) QO)
    (hscore : child - r ^ 2 =
      e + (8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 / 2 + ell * QO / 2 + V / 2 +
        (ell - 1) * (b + A + z) ^ 2 / 4 - (r - A) * cI - ((r - z) / z) * CJ +
        ((r - A) * (r - z) / z) * Phi - (A + b) * FJ / (2 * z)) :
    False := by
  let T := b + A + z
  let rho := (8 / 5 - ell) / (ell - 1)
  let X := A / T
  let t := z / T
  let y := (1 / 5 : ℝ) ^ 2 / T ^ 2
  let B := (8 / 5 - ell) * (T ^ 2 - (1 / 5 : ℝ) ^ 2) / 2
  let P := (8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 / 2 + (ell - 1) * T ^ 2 / 4
  have hell1 : 0 < ell - 1 := by linarith [hell.1]
  have hdelta : 0 < 8 / 5 - ell := by linarith [hell.2]
  have hT : 0 < T := by dsimp [T]; linarith
  have hTlo : 1 / 5 < T := hone
  have hThi : T < 2 / 5 := htwo
  have hT0 : T ≠ 0 := hT.ne'
  have hell0 : ell - 1 ≠ 0 := hell1.ne'
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  have hrT : r = T / 2 := hr
  have hrho : 0 < rho := div_pos hdelta hell1
  have hrho5 : rho ≤ 5 / 4 := by
    dsimp [rho]
    apply (div_le_iff₀ hell1).mpr
    linarith [hell.1]
  have hX : 0 < X := div_pos hA hT
  have ht : 0 < t := div_pos hz hT
  have hsum : X + t ≤ 1 := by
    dsimp [X, t]
    rw [← add_div, div_le_iff₀ hT]
    dsimp [T]
    linarith
  have hhead' : 2 * (1 - t) / 3 ≤ X := by
    dsimp [X, t]
    apply (le_div_iff₀ hT).mpr
    field_simp
    dsimp [T]
    linarith
  have hy : 1 / 4 ≤ y := by
    dsimp [y]
    apply (le_div_iff₀ hT2).mpr
    nlinarith only [hTlo, hThi]
  have hy1 : y < 1 := by
    dsimp [y]
    apply (div_lt_iff₀ hT2).mpr
    nlinarith only [hTlo]
  have hsquare' : (1 - t) ^ 2 ≤ y := by
    have heq : (1 - t) ^ 2 = (A + b) ^ 2 / T ^ 2 := by
      dsimp [t, T]
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hsquare hT2.le
  have hreserve' : rho * y ≤ 11 / 4 * X ^ 2 := by
    have hp := mul_nonneg (sq_nonneg A)
      (by linarith [hell.1] : (0 : ℝ) ≤ 11 / 4 * (ell - 1) - (2 - ell))
    have hres : (8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 ≤
        11 / 4 * (ell - 1) * A ^ 2 := by linarith
    have hscale := mul_le_mul_of_nonneg_right hres
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hell1.le hT2.le))
    convert hscale using 1 <;> dsimp [rho, y, X] <;> field_simp
  obtain ⟨hI, hJ, hstar⟩ := coefficient_bounds hrho hrho5 hX ht hsum hhead' hy hy1 hsquare' hreserve'
  have hI' : B * (r - A) ≤ A * P := by
    rw [hrT]
    have hs := mul_le_mul_of_nonneg_left hI
      (mul_nonneg hell1.le (div_nonneg (pow_nonneg hT.le 3) (by norm_num : (0 : ℝ) ≤ 2)))
    convert hs using 1 <;> dsimp [B, P, rho, y, X] <;> field_simp
    ring
  have hJ' : B * (r - z) ≤ z * P := by
    rw [hrT]
    have hs := mul_le_mul_of_nonneg_left hJ
      (mul_nonneg hell1.le (div_nonneg (pow_nonneg hT.le 3) (by norm_num : (0 : ℝ) ≤ 2)))
    convert hs using 1 <;> dsimp [B, P, rho, y, t] <;> field_simp
    ring
  have hstar' : B * (-(r - A) * (r - z) + (A + b) * (A + z)) ≤
      z * P * (2 * A + z) := by
    rw [hrT]
    have hs := mul_le_mul_of_nonneg_left hstar
      (mul_nonneg hell1.le (div_nonneg (pow_nonneg hT.le 4) (by norm_num : (0 : ℝ) ≤ 2)))
    convert hs using 1 <;> dsimp [B, P, rho, y, X, t, T] <;> field_simp <;> ring
  have hB : 0 < B := by
    dsimp [B]
    have hs : (1 / 5 : ℝ) ^ 2 < T ^ 2 := by nlinarith only [hTlo]
    exact div_pos (mul_pos hdelta (sub_pos.mpr hs)) (by norm_num)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hr0 : 0 ≤ r := by rw [hr]; dsimp [T] at hT; linarith
  have hC : B * (-(r - A) * (r - z)) ≤ z * P * A := by
    rcases le_total r z with hrz | hzr
    · have hi := mul_le_mul_of_nonneg_right hI' (sub_nonneg.mpr hrz)
      have hp := mul_nonneg (mul_nonneg hA.le hP) hr0
      nlinarith only [hi, hp]
    · rcases le_total A r with hAr | hrA
      · have hn := mul_nonneg (mul_nonneg hB.le (sub_nonneg.mpr hAr)) (sub_nonneg.mpr hzr)
        have hp := mul_nonneg (mul_nonneg hz.le hP) hA.le
        nlinarith only [hn, hp]
      · have hj := mul_le_mul_of_nonneg_right hJ' (sub_nonneg.mpr hrA)
        have hp := mul_nonneg (mul_nonneg hz.le hP) hr0
        nlinarith only [hj, hp]
  have hpair : B * (-(r - A) * (r - z) * Phi + (A + b) * FJ / 2) ≤
      z * P * (A * Phi + FJ / 2) := by
    rcases le_total (B * (A + b)) (z * P) with hrate | hrate
    · have hp := mul_le_mul_of_nonneg_right hC hPhi
      have hf := mul_le_mul_of_nonneg_right hrate (by linarith : (0 : ℝ) ≤ FJ / 2)
      nlinarith only [hp, hf]
    · have hp := mul_le_mul_of_nonneg_right hstar' hPhi
      have hf := mul_le_mul_of_nonneg_left htrace (sub_nonneg.mpr hrate)
      nlinarith only [hp, hf]
  have hloss : B * (z * (r - A) * cI + (r - z) * CJ -
        (r - A) * (r - z) * Phi + (A + b) * FJ / 2) ≤
      (z * P) * (A * cI + CJ + A * Phi + FJ / 2) + B * 0 := by
    have hi := mul_le_mul_of_nonneg_right hI' (mul_nonneg hz.le hcI)
    have hj := mul_le_mul_of_nonneg_right hJ' hCJ
    nlinarith only [hi, hj, hpair]
  have hfullNorm : (2 - ell) * rho * (1 - y) ≤ (8 / 5 - ell) * y + ell / 2 := by
    have hprod := mul_le_mul_of_nonneg_right hrho5
      (by linarith [hell.2] : (0 : ℝ) ≤ 7 / 4 - ell)
    have hyprod := mul_le_mul_of_nonneg_left hy hrho.le
    have heq : rho * (ell - 1) = 8 / 5 - ell := by
      dsimp [rho]
      field_simp
    have heqy := congrArg (fun u : ℝ => u * y) heq
    nlinarith only [hprod, hyprod, heqy, hell.1]
  have hfull : (2 - ell) * ((8 / 5 - ell) * (T ^ 2 - (1 / 5 : ℝ) ^ 2) / 2) * z +
      (ell - 1) * 0 ≤
      (ell - 1) * z * ((8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 / 2 + ell * T ^ 2 / 4) := by
    have hs := mul_le_mul_of_nonneg_left hfullNorm
      (div_nonneg (mul_nonneg (mul_nonneg hell1.le hT2.le) hz.le) (by norm_num : (0 : ℝ) ≤ 2))
    convert hs using 1 <;> dsimp [rho, y] <;> field_simp <;> ring
  have hzscore : z * (child - r ^ 2) =
      z * (e + V / 2 + (8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 / 2 + ell * QO / 2 +
        (ell - 1) * T ^ 2 / 4) -
      (z * (r - A) * cI + (r - z) * CJ - (r - A) * (r - z) * Phi + (A + b) * FJ / 2) := by
    rw [hscore]
    dsimp [T]
    field_simp
    ring
  have hBUD : 0 ≤ A * cI + CJ + A * Phi + FJ / 2 := by
    positivity
  have hspent : e + V / 2 + (A * cI + CJ + A * Phi + FJ / 2) + (ell - 1) * QO / 2 ≤
      (8 / 5 - ell) * (T ^ 2 - (1 / 5 : ℝ) ^ 2) / 2 := by
    rw [hE] at hbudget
    dsimp [T]
    linarith
  have hzero : (z * P) * ((8 / 5 - ell) * (T ^ 2 - (1 / 5 : ℝ) ^ 2) / 2) + B * 0 ≤
      B * z * ((8 / 5 - ell) * (1 / 5 : ℝ) ^ 2 / 2 + (ell - 1) * T ^ 2 / 4) := by
    dsimp [B, P]
    ring_nf
    exact le_rfl
  exact not_le.mpr (CuspSourcePeakPayment.child_payment
    (δ := 8 / 5 - ell) (a := 1 / 5) (T := T) (N := z * P) (D := B) (X := 0)
    hz hB (mul_nonneg hz.le hP) (by linarith [hell.1]) he hV hBUD hQO
    (by dsimp [T]; rw [hr]; ring) hzscore hspent hloss hzero hfull) hcost

end Erdos1017.CuspFiveSourcePeakPayment
