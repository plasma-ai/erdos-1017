module

public import Erdos1017.Exclusions.Cusp.CuspThreeDominantScalar

/-!
# Dominant payment contradiction at the third cusp

The marked payment and same-body trace imply the necessary dominant inequality,
with no additional resource or sign assumed (`dominant_payment_contradiction`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CuspThreeDominantPayment

/-- The actual marked payment and same-body trace imply the
necessary dominant inequality. No additional resource or sign is assumed. -/
theorem dominant_payment_contradiction {A b r ell gamma tau n H C L X R : ℝ}
    (hA : 11 / 39 ≤ A) (hb : 0 < b) (hr : 0 ≤ r) (hrb : r ≤ b / 20)
    (hsum : A + b ≤ 1 / 3) (hell : ell ∈ Set.Ioo (5 / 6 : ℝ) 1)
    (hgamma : (4 / 3 - ell) / 9 ≤ gamma)
    (htau : 0 < tau) (hn : 0 ≤ n) (hncap : n ≤ 1 - A - b)
    (hH : 0 ≤ H) (hHcap : H ≤ 1 / 9 - (A + b) ^ 2)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hX : 0 < X)
    (hR : R ≤ L - C) (hCL : 2 * C ≤ L)
    (hpay : (ell * b - r) * tau ≤ R)
    (htrace : (A - Real.sqrt (2 * H)) * X + (gamma - r) * L ≤ 2 * b * C)
    (hCS : 2 * C ^ 2 ≤ tau * n * X) : False := by
  let d := A - Real.sqrt (2 * H)
  let d₀ := A - Real.sqrt (2 * (1 / 9 - (A + b) ^ 2))
  let p := 2 * b - gamma + r
  let g := (ell * b - r) * (gamma - r)
  have hbcap : b ≤ 2 / 39 := by linarith only [hA, hsum]
  have hrcap : r ≤ 1 / 390 := by linarith only [hrb, hbcap]
  have hkr : 0 < 1 / 27 - r := by linarith only [hrcap]
  have hbr : 0 < b - r := by linarith only [hb, hrb]
  have hgam : 1 / 27 ≤ gamma := by linarith only [hgamma, hell.2]
  have hgr : 0 < gamma - r := lt_of_lt_of_le hkr (by linarith only [hgam])
  have helb : 0 < ell * b - r := by
    nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hell.1.le), hb, hrb]
  have hg : 0 < g := mul_pos helb hgr
  have hrad : 0 ≤ 1 / 9 - (A + b) ^ 2 := hH.trans hHcap
  have hs₀ := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrad)
  have hd₀ : 0 < d₀ := by
    dsimp only [d₀]
    nlinarith only [hs₀, Real.sqrt_nonneg (2 * (1 / 9 - (A + b) ^ 2)),
      hA, hb, sq_nonneg (A - 11 / 39), mul_nonneg (by linarith only [hA] : 0 ≤ A) hb.le]
  have hdle : d₀ ≤ d := by
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hHcap (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [d₀, d]
    linarith only [hs]
  have hd : 0 < d := hd₀.trans_le hdle
  change d * X + (gamma - r) * L ≤ 2 * b * C at htrace
  have hdX : 0 < d * X := mul_pos hd hX
  have hbg : gamma - r < b := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hL
    have hc := mul_le_mul_of_nonneg_left hCL hb.le
    nlinarith only [hm, hc, htrace, hdX]
  have hlarge : 1 / 27 ≤ b + r := by linarith only [hbg, hgam]
  have hp : 0 < p := by dsimp only [p]; linarith only [hbg, hb]
  have hcombined : d * X + g * tau ≤ p * C := by
    have hm := mul_le_mul_of_nonneg_left (hpay.trans hR) hgr.le
    dsimp only [g, p]
    nlinarith only [hm, htrace]
  have hleft : 0 ≤ d * X + g * tau := by positivity
  have hright : 0 ≤ p * C := mul_nonneg hp.le hC
  have hsquare : (d * X + g * tau) ^ 2 ≤ (p * C) ^ 2 :=
    pow_le_pow_left₀ hleft hcombined 2
  have hcs := mul_le_mul_of_nonneg_left hCS (sq_nonneg p)
  have hprod : (8 * g * d) * (tau * X) ≤ (n * p ^ 2) * (tau * X) := by
    nlinarith only [hsquare, hcs, sq_nonneg (d * X - g * tau)]
  have hnecessary : 8 * g * d ≤ n * p ^ 2 :=
    (mul_le_mul_iff_left₀ (mul_pos htau hX)).mp hprod
  have hcoupled : (b - r) * (1 / 27 - r) ≤ g := by
    have hbase := mul_le_mul_of_nonneg_left hgamma helb.le
    have hbracket : 0 ≤ b * (ell / 9 - 1 / 27 + r) - r / 9 := by
      nlinarith only [mul_nonneg hb.le (sub_nonneg.mpr hell.1.le),
        mul_nonneg hb.le hr, hrb, hb]
    have hid : (ell * b - r) * ((4 / 3 - ell) / 9 - r) -
        (b - r) * (1 / 27 - r) =
        (1 - ell) * (b * (ell / 9 - 1 / 27 + r) - r / 9) := by ring
    have hnonneg := mul_nonneg (sub_nonneg.mpr hell.2.le) hbracket
    dsimp only [g]
    nlinarith only [hbase, hid, hnonneg]
  have hlow : 8 * (b - r) * (1 / 27 - r) * d₀ ≤ 8 * g * d := by
    have hfirst := mul_le_mul_of_nonneg_left hdle
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (mul_pos hbr hkr).le)
    have hsecond := mul_le_mul_of_nonneg_right hcoupled hd.le
    nlinarith only [hfirst, hsecond]
  have hpcap : p ≤ 2 * b - 1 / 27 + r := by dsimp only [p]; linarith only [hgam]
  have hpsq : p ^ 2 ≤ (2 * b - 1 / 27 + r) ^ 2 :=
    pow_le_pow_left₀ hp.le hpcap 2
  have hupper : n * p ^ 2 ≤ (1 - A - b) * (2 * b - 1 / 27 + r) ^ 2 :=
    (mul_le_mul_of_nonneg_left hpsq hn).trans
      (mul_le_mul_of_nonneg_right hncap (sq_nonneg _))
  exact CuspThreeDominantScalar.dominant_contradiction hA hb hrb hsum hlarge
    (hlow.trans (hnecessary.trans hupper))

end Erdos1017.CuspThreeDominantPayment
