module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalContract

/-!
# Price bounds at the certificate floor margin

Lowering the margin to the certificate floor only weakens the moment and
zero-price licenses, bounds the signed price by the certificate price at the
same radius, atom cap, hole mass and paid error, and only increases the
negative-row radius.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MiddleE2LargeUniversal.Point

/-- The cancelled certificate pole is the same single relaxed atom denominator. -/
theorem price_pole_eq (X : Point) : X.pole = X.A - X.RC - X.C := by
  have hRC : X.RC ≤ 1 - 3 * X.A + X.b := min_le_left _ _
  have hC : X.C ≤ 1 - 2 * X.A - X.b := by
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hid : X.A - X.RC - X.C =
      max (max (3 * X.A + X.b - 1 - X.RC) (X.b + X.K - X.RC))
        (X.A + X.b - X.T - X.RC) := by
    dsimp only [C, r0]
    rw [← max_sub_sub_left, ← max_sub_sub_left]
    congr 1
    · congr 1 <;> ring
    · ring
  have hlast : 6 * X.A - 2 ≤ X.A - X.RC - X.C := by
    linarith only [hRC, hC]
  unfold pole
  rw [← max_assoc, ← hid, max_eq_left hlast]

/-- Lowering the original margin to the certificate floor only weakens the
moment and zero-price licenses, at the same relaxed radius and atom cap. -/
theorem actual_price_licenses {X : Point} {gamma DH : ℝ}
    (hnecessary : X.Necessary) (htests : X.PriceTests)
    (hA : 0 < X.A) (hgamma : X.g ≤ gamma)
    (hDH : 0 ≤ DH) (hbudget : DH ≤ X.de * X.p) :
    let theta := 3 * gamma / X.A - X.de
    0 < X.A - X.RC - X.C ∧ 0 < X.A - X.RC ∧ 0 < theta ∧
      DH < theta * (X.A - X.RC) ∧ max 0 (1 - 2 * theta) * X.RC < gamma := by
  rcases hnecessary with ⟨_, _, _, _, _, _, _, _, hRC, _, hC, _⟩
  rcases htests with ⟨hpole, _, _, hmoment, hzero, _⟩
  let theta := 3 * gamma / X.A - X.de
  have htheta : X.theta ≤ theta := by
    exact sub_le_sub_right
      (div_le_div_of_nonneg_right (by linarith only [hgamma]) hA.le) X.de
  rw [price_pole_eq] at hpole
  have hk : 0 < X.A - X.RC := by linarith only [hpole, hC]
  have hpaid : DH < theta * (X.A - X.RC) := by
    have hscale := mul_le_mul_of_nonneg_right htheta hk.le
    dsimp only [moment] at hmoment
    linarith only [hmoment, hbudget, hscale]
  have htheta0 : 0 < theta :=
    (mul_pos_iff_of_pos_right hk).mp (hDH.trans_lt hpaid)
  have hmax : max 0 (1 - 2 * theta) ≤ max 0 (1 - 2 * X.theta) :=
    max_le_max le_rfl (by linarith only [htheta])
  have hzero' : max 0 (1 - 2 * theta) * X.RC < gamma := by
    have hscale := mul_le_mul_of_nonneg_right hmax hRC
    dsimp only [zeroprice] at hzero
    linarith only [hscale, hzero, hgamma]
  exact ⟨hpole, hk, htheta0, hpaid, hzero'⟩

/-- The original signed price is bounded by the certificate price using
the same radius, atom cap, hole mass and paid error. -/
theorem actual_price_bill_le {X : Point} {gamma error : ℝ}
    (htests : X.PriceTests) (heta : 0 ≤ X.eta)
    (hgamma : X.g ≤ gamma) (herror : error ≤ X.E) :
    max 0 (X.b * X.ell - gamma) * X.eta / X.pole +
      X.ell * (X.RC - X.A + X.b) - gamma + error ≤ X.G := by
  have hmax : max 0 (X.b * X.ell - gamma) ≤ max 0 (X.b * X.ell - X.g) :=
    max_le_max le_rfl (by linarith only [hgamma])
  have hscaled := mul_le_mul_of_nonneg_right hmax heta
  have hdiv := div_le_div_of_nonneg_right hscaled htests.1.le
  dsimp only [G]
  linarith only [hdiv, hgamma, herror]

private theorem error_le_row_cap {A ell gamma u kappa good : ℝ}
    (hA : 0 < A) (hRR : 0 < (2 * ell - 1) * A + 3 * gamma)
    (hu : 0 < u) (hkappa : 0 ≤ kappa) (hgood0 : 0 ≤ good)
    (hmargin : u + kappa ≤ 1 - 2 * A)
    (hgood : (ell + (3 * gamma / A - (1 - ell))) * good ≤
      2 * ell * u - (ell + gamma - (1 + ell) * A)) :
    let theta := 3 * gamma / A - (1 - ell)
    let RP := ell + gamma - (1 + ell) * A
    let RR := (2 * ell - 1) * A + 3 * gamma
    kappa * max (ell - theta) 0 * good / u ≤
      max 0 (A - 3 * gamma) / RR * (1 - 2 * A - u) * max 0 (2 * ell - RP / u) := by
  let theta := 3 * gamma / A - (1 - ell)
  let RP := ell + gamma - (1 + ell) * A
  let RR := (2 * ell - 1) * A + 3 * gamma
  let T := A - 3 * gamma
  let r0 := 1 - 2 * A
  have hucap : u ≤ r0 := by dsimp only [r0]; linarith only [hmargin, hkappa]
  by_cases htau : 0 < ell - theta
  · have hTidentity : A * (ell - theta) = T := by
      dsimp only [theta, T]
      field_simp [hA.ne']
      ring
    have hT : 0 < T := hTidentity ▸ mul_pos hA htau
    have hRidentity : A * (ell + theta) = RR := by
      dsimp only [theta, RR]
      field_simp [hA.ne']
      ring
    have hgoodscaled := mul_le_mul_of_nonneg_left hgood hA.le
    have hRscaled := congrArg (fun x : ℝ => x * good) hRidentity
    have hgood' : RR * good ≤ A * (2 * ell * u - RP) := by
      dsimp only [theta, RP] at *
      nlinarith only [hgoodscaled, hRscaled]
    have hw : 0 ≤ 2 * ell * u - RP := by
      have hnonnegative : 0 ≤ A * (2 * ell * u - RP) :=
        (mul_nonneg hRR.le hgood0).trans hgood'
      exact (mul_nonneg_iff_of_pos_left hA).mp hnonnegative
    have hscaled := mul_le_mul_of_nonneg_left hgood' (mul_nonneg hkappa htau.le)
    have hTscaled := congrArg (fun x : ℝ => kappa * x * (2 * ell * u - RP)) hTidentity
    have hkpaid := mul_nonneg
      (show 0 ≤ r0 - u - kappa by dsimp only [r0]; linarith only [hmargin])
      (mul_nonneg hT.le hw)
    have hrow : kappa * (ell - theta) * good * RR ≤
        T * (r0 - u) * (2 * ell * u - RP) := by
      nlinarith only [hscaled, hTscaled, hkpaid]
    have hratio : kappa * (ell - theta) * good / u ≤
        T / RR * (r0 - u) * (2 * ell - RP / u) := by
      have heq : T / RR * (r0 - u) * (2 * ell - RP / u) =
          T * (r0 - u) * (2 * ell * u - RP) / (RR * u) := by
        field_simp [hRR.ne', hu.ne']
      rw [heq]
      apply (div_le_div_iff₀ hu (mul_pos hRR hu)).mpr
      have h := mul_le_mul_of_nonneg_right hrow hu.le
      nlinarith only [h]
    have heqrow : (2 * ell * u - RP) / u = 2 * ell - RP / u := by
      field_simp [hu.ne']
    have hrow0 : 0 ≤ 2 * ell - RP / u := by
      rw [← heqrow]
      exact div_nonneg hw hu.le
    change kappa * max (ell - theta) 0 * good / u ≤
      max 0 T / RR * (r0 - u) * max 0 (2 * ell - RP / u)
    rw [max_eq_left htau.le, max_eq_right hT.le, max_eq_right hrow0]
    exact hratio
  · change kappa * max (ell - theta) 0 * good / u ≤ _
    rw [max_eq_right (le_of_not_gt htau), mul_zero, zero_mul, zero_div]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (le_max_left _ _) hRR.le)
        (show 0 ≤ 1 - 2 * A - u by linarith only [hucap]))
      (le_max_left _ _)

/-- The actual same-mass error is paid by the relaxed error at the floor
margin. The common-region mass is retained in both numerator and denominator. -/
theorem actual_error_le {X : Point} {gamma kappa good : ℝ}
    (hA : 0 < X.A) (hell : 1 / 2 < X.ell) (hg : 0 < X.g) (hu : 0 < X.u)
    (hgamma : X.g ≤ gamma) (hkappa : 0 ≤ kappa) (hgood0 : 0 ≤ good)
    (hmargin : X.u + kappa ≤ X.r0)
    (hresource : (X.ell + (3 * gamma / X.A - X.de)) * good ≤
      2 * X.ell * X.u - (X.ell + gamma - (1 + X.ell) * X.A)) :
    kappa * max (X.ell - (3 * gamma / X.A - X.de)) 0 * good / X.u ≤ X.E := by
  have htheta : 3 * X.g / X.A - X.de ≤ 3 * gamma / X.A - X.de := by
    exact sub_le_sub_right
      (div_le_div_of_nonneg_right (by linarith only [hgamma]) hA.le) X.de
  have hscale := mul_le_mul_of_nonneg_right htheta hgood0
  have hresource0 : (X.ell + (3 * X.g / X.A - (1 - X.ell))) * good ≤
      2 * X.ell * X.u - (X.ell + X.g - (1 + X.ell) * X.A) := by
    change (X.ell + (3 * X.g / X.A - X.de)) * good ≤ _
    linarith only [hresource, hscale, hgamma]
  have hRR : 0 < (2 * X.ell - 1) * X.A + 3 * X.g := by
    have hcoef : 0 < 2 * X.ell - 1 := by linarith only [hell]
    positivity
  have hbound := error_le_row_cap hA hRR hu hkappa hgood0 hmargin hresource0
  dsimp only at hbound
  have hRP : X.ell + X.g - (1 + X.ell) * X.A = X.RP := by
    dsimp only [RP]
    ring
  rw [hRP] at hbound
  change kappa * max (X.ell - (3 * X.g / X.A - X.de)) 0 * good / X.u ≤ X.E at hbound
  have htau : max (X.ell - (3 * gamma / X.A - X.de)) 0 ≤
      max (X.ell - (3 * X.g / X.A - X.de)) 0 :=
    max_le_max (by linarith only [htheta]) le_rfl
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htau hkappa) hgood0
  exact (div_le_div_of_nonneg_right hnum hu.le).trans hbound

/-- The same negative-row radius only increases when its margin is lowered. -/
theorem actual_radius_le {X : Point} {gamma : ℝ}
    (hell : 0 < X.ell) (hgamma : X.g ≤ gamma) :
    min (1 - 3 * X.A + X.b)
      ((1 - X.u - 2 * X.ell * X.A - 3 * gamma) / X.ell) ≤ X.RC := by
  exact min_le_min le_rfl
    (div_le_div_of_nonneg_right (by linarith only [hgamma]) hell.le)

end Erdos1017.MiddleE2LargeUniversal.Point
