module

public import Erdos1017.Exclusions.Cusp.BenchmarkSplitCubicEnvelopes

/-!
# Scalar exit for the fourth-cusp outside peak

Both outside sectors at the fourth cusp are excluded by the reverse and forward
split comparisons with the same original inventory (`outside_contradiction`).
-/

@[expose] public section

namespace Erdos1017.CuspFourOutsidePeakScalar

private theorem low_exit {delta R : ℝ} (hd : 0 < delta) (hdc : delta ≤ 1 / 3)
    (hR : 0 < R) (hRc : R < 2 * delta)
    (hf : delta < (1 / 2 + delta) * R ^ 2 - (19 / 40) * R ^ 3) : False := by
  have hR2 : R ≤ 2 / 3 := by linarith only [hRc, hdc]
  have hbracket : 0 ≤ (1 / 2 + delta) * (2 * delta + R) -
      (19 / 40) * ((2 * delta) ^ 2 + 2 * delta * R + R ^ 2) := by
    have hp := mul_nonneg hR.le (show 0 ≤ 2 / 3 - R by linarith only [hR2])
    have hm := mul_nonneg hd.le hR.le
    nlinarith [sq_nonneg delta]
  have hmono := mul_nonneg (show 0 ≤ 2 * delta - R by linarith only [hRc]) hbracket
  have hd2 := mul_nonneg hd.le (show 0 ≤ 1 / 3 - delta by linarith only [hdc])
  have hd3 := mul_nonneg (sq_nonneg delta) (show 0 ≤ 1 / 3 - delta by linarith only [hdc])
  nlinarith only [hf, hmono, hd2, hd3, hd]

private theorem above_fifth {delta R : ℝ} (hd : 1 / 3 ≤ delta) (hR : 0 < R)
    (hf : delta < (1 / 2 + delta) * R ^ 2 - (19 / 40) * R ^ 3) : 4 / 5 < R := by
  by_contra hn
  have hRc : R ≤ 4 / 5 := le_of_not_gt hn
  have hbracket : 0 ≤ (1 / 2 + delta) * (4 / 5 + R) -
      (19 / 40) * ((4 / 5 : ℝ) ^ 2 + (4 / 5) * R + R ^ 2) := by
    have hp := mul_nonneg hR.le (show 0 ≤ 4 / 5 - R by linarith only [hRc])
    have hm := mul_nonneg (show 0 ≤ delta - 1 / 3 by linarith only [hd]) hR.le
    nlinarith only [hp, hm, hd]
  have hmono := mul_nonneg (show 0 ≤ 4 / 5 - R by linarith only [hRc]) hbracket
  nlinarith only [hf, hmono, hd]

set_option maxHeartbeats 800000 in
/-- Both fourth-cusp outside sectors are excluded from literal reverse
and forward split comparisons and their same original inventory. -/
theorem outside_contradiction {delta R H T Q : ℝ}
    (hd : delta ∈ Set.Ioo (0 : ℝ) (2 / 5)) (hR : 0 < R)
    (hH : H = T ^ 2 + Q) (hT : 1 / 4 < T) (hHcap : H < 5 / 32)
    (hAQ : (R / 4) ^ 2 ≤ Q)
    (hvariance : (1 / 2 - delta) * Q < delta * (T ^ 2 - 1 / 16))
    (hproduct : delta / 16 < (1 / 2 + delta) * H - 2 * Q)
    (hreverse : 0 < Benchmark.splitValue (Real.sqrt H) - 3 / 64 -
      (3 / 2 - delta) * (H - 1 / 16) / 2)
    (hforward : delta < 16 * (2 * Benchmark.splitValue (R / 4) -
      (3 / 2 - delta) * (R / 4) ^ 2)) : False := by
  have hdelta0 : 0 < delta := hd.1
  have hQ : 0 ≤ Q := (sq_nonneg (R / 4)).trans hAQ
  have hH0 : 0 ≤ H := by nlinarith only [hH, hQ]
  have hs : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt hH0
  have hr0 := Real.sqrt_nonneg H
  have hrlo : 1 / 4 < Real.sqrt H := by nlinarith only [hs, hH, hQ, hT, hr0]
  have hp := mul_lt_mul_of_pos_left hHcap (show 0 < 1 / 2 + delta by linarith only [hd.1])
  have hRcap : R ^ 2 < 5 / 8 + 3 * delta / 4 := by nlinarith only [hp, hproduct, hAQ]
  have hRone : R < 1 := by nlinarith only [hRcap, hd.2, hR]
  have hcurve := Benchmark.splitValue_le_nineteen_twentieths (r := R / 4)
    ⟨by positivity, by linarith only [hRone]⟩
  have hf : delta < (1 / 2 + delta) * R ^ 2 - (19 / 40) * R ^ 3 := by
    nlinarith only [hforward, hcurve]
  by_cases hdlo : delta ≤ 1 / 3
  · have hthird : Real.sqrt H < 1 / 3 := by
      by_contra hn
      have hc : Real.sqrt H ∈ Set.Icc (1 / (((1 : ℕ) : ℝ) + 2))
          (1 / (((1 : ℕ) : ℝ) + 1)) := by
        constructor
        · norm_num; exact le_of_not_gt hn
        · norm_num; nlinarith only [hs, hHcap, hr0]
      have hg := hreverse
      rw [Benchmark.splitValue_on_cell 1 hc] at hg
      norm_num [Benchmark.splitPolynomial] at hg
      have hm := mul_nonneg (show 0 ≤ 1 / 3 - delta by linarith only [hdlo])
        (show 0 ≤ H - 1 / 16 by nlinarith only [hH, hQ, hT])
      nlinarith [sq_nonneg (17 * Real.sqrt H - 6)]
    have hc : Real.sqrt H ∈ Set.Icc (1 / (((2 : ℕ) : ℝ) + 2))
        (1 / (((2 : ℕ) : ℝ) + 1)) := by
      constructor <;> norm_num
      · exact hrlo.le
      · exact hthird.le
    have hg := hreverse
    rw [Benchmark.splitValue_on_cell 2 hc] at hg
    norm_num [Benchmark.splitPolynomial] at hg
    let x := 4 * Real.sqrt H
    have hx : 1 < x := by dsimp [x]; linarith only [hrlo]
    have hxs : x ^ 2 = 16 * H := by dsimp [x]; rw [mul_pow, hs]; norm_num
    have hm := congrArg (fun z : ℝ => delta * z) hs
    have hprod : 0 < (x - 1) * ((8 + 3 * delta) - (8 - 3 * delta) * x) := by
      dsimp [x]
      nlinarith only [hg, hs, hm]
    have hb := (mul_pos_iff_of_pos_left (sub_pos.mpr hx)).mp hprod
    have hden : 7 ≤ 8 - 3 * delta := by linarith only [hdlo]
    have hsq : (8 - 3 * delta) ^ 2 * x ^ 2 < (8 + 3 * delta) ^ 2 := by
      have hpos : 0 ≤ (8 - 3 * delta) * x := by positivity
      have h := (sq_lt_sq₀ hpos (by positivity : 0 ≤ 8 + 3 * delta)).mpr
        (show (8 - 3 * delta) * x < 8 + 3 * delta by linarith only [hb])
      nlinarith only [h]
    have hsmall : R ^ 2 < 2 * delta * (x ^ 2 - 1) := by
      rw [hxs, hH]
      nlinarith only [hvariance, hAQ]
    have hscale := mul_lt_mul_of_pos_left hsmall
      (sq_pos_of_pos (show 0 < 8 - 3 * delta by linarith only [hden]))
    have hxscale := mul_lt_mul_of_pos_left hsq (mul_pos (by norm_num : (0 : ℝ) < 2) hd.1)
    have hfinal : (8 - 3 * delta) ^ 2 * R ^ 2 < 192 * delta ^ 2 := by
      nlinarith only [hscale, hxscale]
    have hdR := mul_nonneg (sq_nonneg R)
      (show 0 ≤ (8 - 3 * delta) ^ 2 - 49 by nlinarith only [hden])
    have hRc : R < 2 * delta := by nlinarith only [hfinal, hdR, hR, hd.1]
    exact low_exit hd.1 hdlo hR hRc hf
  · have hdhi : 1 / 3 ≤ delta := (lt_of_not_ge hdlo).le
    have hRlo := above_fifth hdhi hR hf
    have hc : R / 4 ∈ Set.Icc (1 / (((3 : ℕ) : ℝ) + 2))
        (1 / (((3 : ℕ) : ℝ) + 1)) := by
      constructor <;> norm_num <;> linarith only [hRlo, hRone]
    have hg := hforward
    rw [Benchmark.splitValue_on_cell 3 hc] at hg
    norm_num [Benchmark.splitPolynomial] at hg
    have hprod : 0 < (1 - R) * ((12 - 5 * delta) * R - (8 + 5 * delta)) := by
      nlinarith only [hg]
    have hb := (mul_pos_iff_of_pos_left (sub_pos.mpr hRone)).mp hprod
    have hden : 0 < 12 - 5 * delta := by linarith only [hd.2]
    have hsquare : (8 + 5 * delta) ^ 2 < (12 - 5 * delta) ^ 2 * R ^ 2 := by
      have hp0 : 0 ≤ 8 + 5 * delta := by positivity
      have hp1 : 0 ≤ (12 - 5 * delta) * R := mul_nonneg hden.le hR.le
      have h := (sq_lt_sq₀ hp0 hp1).mpr
        (show 8 + 5 * delta < (12 - 5 * delta) * R by linarith only [hb])
      nlinarith only [h]
    let u := delta - 1 / 3
    have hu : 0 ≤ u := sub_nonneg.mpr hdhi
    have huc : u ≤ 1 / 15 := by dsimp [u]; linarith only [hd.2]
    have hpoly : 0 < -208 + 376 * delta + 795 * delta ^ 2 - 150 * delta ^ 3 := by
      have hp := mul_nonneg (sq_nonneg u) (show 0 ≤ 645 - 150 * u by linarith only [huc])
      dsimp [u] at hp hu
      nlinarith only [hp, hu]
    have hscaled := mul_lt_mul_of_pos_left hRcap (sq_pos_of_pos hden)
    nlinarith only [hsquare, hscaled, hpoly]

end Erdos1017.CuspFourOutsidePeakScalar
