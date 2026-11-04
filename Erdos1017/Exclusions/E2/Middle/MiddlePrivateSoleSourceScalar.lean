module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Scalar facts for the middle private sole source

On the closed no-saturation range the own multiplier is at least `9/11`, the
missing mass is below `1/4`, the peak floor `A > 61/200` holds and the curvature
ratio stays below `882/1163` on `z ≤ 21/40`; these combine with the scaled Schur
bound into the sole-source contradiction. A failed-insertion margin is also
proved.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddlePrivateSoleSourceScalar

open LowerE2Scalar

/-- On the closed no-saturation range the own multiplier is at least `9/11`. -/
theorem multiplier_ge {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    9 / 11 ≤ multiplier q := by
  unfold multiplier
  rw [le_div_iff₀ (by linarith [hq.1])]
  linarith [hq.2]

/-- On the closed no-saturation range the stationary missing mass is below `1/4`.
Cleared, `44q^4 + 112q^3 - 132q^2 - 32q + 8 < 0`. -/
theorem missingMass_lt_quarter {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    missingMass q < 1 / 4 := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have h2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  have h3 : q ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := pow_le_pow_left₀ hq0 hq.2 3
  have h4 : q ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hq0 hq.2 4
  have hid : 8 * denominator q ^ 2 - 4 * ((q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2)) =
      -(44 * q ^ 4 + 112 * q ^ 3 - 132 * q ^ 2 - 32 * q + 8) := by
    unfold denominator
    ring
  unfold missingMass
  rw [div_lt_iff₀ (by positivity)]
  norm_num at h2 h3 h4
  nlinarith [hq.1]

/-- The strengthened peak floor `A > 61/200`: on the closed no-saturation
range, `D_ell(A) < g_q` for every `0 <= A <= 61/200`. Cleared at
`A = 61/200`, `-18454 + 56943q + 204393q^2 + 186121q^3 > 0`; the selector
value increases on `[0, 61/200]` since `ell <= 1`. -/
theorem selectorValue_lt_gapFloor_of_le {q A : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hA : A ∈ Icc (0 : ℝ) (61 / 200)) :
    (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 < gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hden : 0 < 2 + q := by linarith
  have hR := denominator_pos hq0
  have hell1 : multiplier q ≤ 1 := by
    unfold multiplier
    rw [div_le_iff₀ hden]
    linarith
  have hell0 : 0 ≤ multiplier q := by
    unfold multiplier
    exact div_nonneg (by linarith [hq.2]) hden.le
  have hbracket : 0 ≤ 8 - (7 + 6 * multiplier q) * (61 / 200 + A) := by
    nlinarith [hA.2, hA.1]
  have hmono : (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 ≤
      (-1 + 8 * (61 / 200) - (7 + 6 * multiplier q) * (61 / 200) ^ 2) / 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA.2) hbracket]
  have h2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  have h3 : (187 / 1000 : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq.1 3
  have hpoly : 0 < -18454 + 56943 * q + 204393 * q ^ 2 + 186121 * q ^ 3 := by
    norm_num at h2 h3
    linarith [hq.1]
  have hfloor : (-1 + 8 * (61 / 200) - (7 + 6 * multiplier q) * (61 / 200) ^ 2) / 6 <
      gapFloor q := by
    have hid : (gapFloor q - (-1 + 8 * (61 / 200) -
        (7 + 6 * multiplier q) * (61 / 200) ^ 2) / 6) *
        (240000 * denominator q * (2 + q)) =
        -18454 + 56943 * q + 204393 * q ^ 2 + 186121 * q ^ 3 := by
      unfold gapFloor multiplier
      field_simp
      unfold denominator
      ring
    have hpos : 0 < 240000 * denominator q * (2 + q) := by positivity
    rw [← hid] at hpoly
    exact sub_pos.mp (pos_of_mul_pos_left hpoly hpos.le)
  linarith

/-- The Schur complement of the three bounded directions with a scaled
exposure. If every combination `wK + y wI + w f` obeys the curvature test
and `ell k < E`, then `ell (ν + C D^2) < 2 C ν k (A+k)`, i.e.
`ell < 2 C_eff k (A + k)` with `C_eff = C ν / (ν + C D^2)`. -/
theorem curvature_schur_scaled {A k D ν C DK E Q ell : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hν : 0 < ν) (hC : 0 < C) (hell : 0 ≤ ell)
    (hDK : DK ≤ k * (A + k)) (hE : ell * k < E) (hQ : 0 ≤ Q)
    (hall : ∀ y w : ℝ, Q + 2 * y * A * E - w ^ 2 * ν ≤
      C * (DK + y * A * k + w * D) ^ 2) :
    ell * (ν + C * D ^ 2) < 2 * C * ν * k * (A + k) := by
  have hΔ : 0 < ν + C * D ^ 2 := by positivity
  have hCν : 0 < C * ν * k := by positivity
  obtain ⟨l, hl⟩ : ∃ l, l = E * (ν + C * D ^ 2) / (C * ν * k) := ⟨_, rfl⟩
  have hkey := hall ((l - DK) / (A * k)) (-(C * l * D / (ν + C * D ^ 2)))
  have h1 : DK + (l - DK) / (A * k) * A * k + -(C * l * D / (ν + C * D ^ 2)) * D =
      l * ν / (ν + C * D ^ 2) := by
    field_simp
    ring
  have h2 : 2 * ((l - DK) / (A * k)) * A * E = 2 * E * (l - DK) / k := by
    field_simp
  have h3 : C * (l * ν / (ν + C * D ^ 2)) ^ 2 +
      (-(C * l * D / (ν + C * D ^ 2))) ^ 2 * ν = l * E / k := by
    rw [hl]
    field_simp
  rw [h1, h2] at hkey
  have hstep : 2 * E * (l - DK) / k ≤ l * E / k := by linarith
  have hEpos : 0 < E := lt_of_le_of_lt (mul_nonneg hell hk.le) hE
  have hl2 : l ≤ 2 * DK := by
    have h := mul_le_mul_of_nonneg_right hstep hk.le
    rw [div_mul_cancel₀ _ hk.ne', div_mul_cancel₀ _ hk.ne'] at h
    by_contra hc
    have hc' : 0 < l - 2 * DK := by linarith
    nlinarith [mul_pos hEpos hc']
  have hEΔ : E * (ν + C * D ^ 2) ≤ 2 * DK * (C * ν * k) := by
    have h := mul_le_mul_of_nonneg_right hl2 hCν.le
    rw [hl, div_mul_cancel₀ _ hCν.ne'] at h
    exact h
  have hDKC : 2 * DK * (C * ν * k) ≤ k * (2 * C * ν * k * (A + k)) := by
    have h := mul_le_mul_of_nonneg_right hDK (show 0 ≤ 2 * (C * ν * k) by positivity)
    nlinarith
  have hlow : ell * k * (ν + C * D ^ 2) < E * (ν + C * D ^ 2) :=
    mul_lt_mul_of_pos_right hE hΔ
  have hfinal : k * (ell * (ν + C * D ^ 2)) < k * (2 * C * ν * k * (A + k)) := by
    nlinarith
  exact lt_of_mul_lt_mul_left hfinal hk.le

/-- The rational curvature function stays below `882/1163` on
`z ≤ 21/40`: `882(1+6(z-1/4)^2) - 13956 z(z-7/20) = 8664(21/40-z)(z+385/1444)`. -/
theorem curvature_ratio_le {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 21 / 40) :
    12 * z * (z - 7 / 20) * 1163 ≤ 882 * (1 + 6 * (z - 1 / 4) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ z + 385 / 1444 by linarith)]

/-- The final sole-source contradiction. With `9/11 <= ell`, `0 < C < 6`,
`0 < ν < 1`, `h < 1/4`, `α = A + b > 7/20`, `z = α + k < 21/40` and the
scaled Schur bound `ell (ν + C (z-h)^2) < 2 C ν k (A+k)`, one would get
`ell < 12 z (z-7/20)/(1+6(z-1/4)^2) <= 882/1163 < 9/11`. -/
theorem sole_source_false {ell C ν h A b k : ℝ}
    (hell : 9 / 11 ≤ ell) (hC : 0 < C) (hC6 : C < 6) (hν : 0 < ν) (hν1 : ν < 1)
    (hh : h < 1 / 4) (hA : 0 < A) (hb : 0 ≤ b) (hk : 0 < k)
    (hα : 7 / 20 < A + b) (hz : A + b + k < 21 / 40)
    (hschur : ell * (ν + C * (A + b + k - h) ^ 2) < 2 * C * ν * k * (A + k)) : False := by
  set z := A + b + k with hzdef
  set s := (z - 1 / 4) ^ 2 with hsdef
  have hD : z - 1 / 4 ≤ z - h := by linarith
  have hD0 : 0 ≤ z - 1 / 4 := by linarith
  have hsq : s ≤ (z - h) ^ 2 := pow_le_pow_left₀ hD0 hD 2
  have hs0 : 0 ≤ s := sq_nonneg _
  have hkz : k ≤ z - 7 / 20 := by linarith
  have hAkz : A + k ≤ z := by linarith
  have hkA : k * (A + k) ≤ (z - 7 / 20) * z :=
    mul_le_mul hkz hAkz (by linarith) (by linarith)
  have hP : 0 < C * ν := mul_pos hC hν
  have hpoly := curvature_ratio_le (z := z) (by linarith) hz.le
  -- Left side: `ell (ν + C s) ≥ (9/11) C ν (1 + 6 s) / 6`.
  have hCs : C * s ≤ C * (z - h) ^ 2 := mul_le_mul_of_nonneg_left hsq hC.le
  have hleft1 : ell * (ν + C * s) ≤ ell * (ν + C * (z - h) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hCs]) (by linarith only [hell])
  have hνC : C * ν < 6 * ν := mul_lt_mul_of_pos_right hC6 hν
  have hsC : 0 ≤ C * s * (1 - ν) := mul_nonneg (mul_nonneg hC.le hs0) (by linarith)
  have hmid : C * ν * (1 + 6 * s) / 6 ≤ ν + C * s := by
    have he : C * ν * (1 + 6 * s) / 6 = C * ν / 6 + C * s - C * s * (1 - ν) := by ring
    rw [he]
    linarith only [hνC, hsC]
  have hpos : 0 ≤ C * ν * (1 + 6 * s) / 6 := by positivity
  have hleft2 : 9 / 11 * (C * ν * (1 + 6 * s) / 6) ≤ ell * (ν + C * s) :=
    calc 9 / 11 * (C * ν * (1 + 6 * s) / 6) ≤ ell * (C * ν * (1 + 6 * s) / 6) :=
          mul_le_mul_of_nonneg_right hell hpos
      _ ≤ ell * (ν + C * s) := mul_le_mul_of_nonneg_left hmid (by linarith only [hell])
  -- Right side: `2 C ν k (A+k) ≤ C ν (147/1163) (1 + 6 s)`.
  have h1 : k * (A + k) * (2 * C * ν) ≤ (z - 7 / 20) * z * (2 * C * ν) :=
    mul_le_mul_of_nonneg_right hkA (by positivity)
  have h2 : (z - 7 / 20) * z ≤ 147 / 1163 / 2 * (1 + 6 * s) := by
    rw [hsdef]
    linarith only [hpoly]
  have h3 : (z - 7 / 20) * z * (2 * C * ν) ≤ 147 / 1163 / 2 * (1 + 6 * s) * (2 * C * ν) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have hQ : 0 < C * ν * (1 + 6 * s) := by positivity
  have hright : 2 * C * ν * k * (A + k) ≤ C * ν * (1 + 6 * s) * (147 / 1163) := by
    have e1 : 2 * C * ν * k * (A + k) = k * (A + k) * (2 * C * ν) := by ring
    have e2 : 147 / 1163 / 2 * (1 + 6 * s) * (2 * C * ν) =
        C * ν * (1 + 6 * s) * (147 / 1163) := by ring
    rw [e1, ← e2]
    exact h1.trans h3
  have hl2' : 9 / 11 * (C * ν * (1 + 6 * s) / 6) = C * ν * (1 + 6 * s) * (3 / 22) := by ring
  rw [hl2'] at hleft2
  linarith only [hleft1, hleft2, hright, hschur, hQ]

/-- The `beta = 0` failed-insertion margin `H(0) > 0`, after eliminating
`f = w - a - b`; it is affine in `a`, so both signs of its slope are handled. -/
private theorem insertion_margin_zero {A γ ℓ a b f L : ℝ}
    (hA : 61 / 200 ≤ A) (hγ : 27 / 500 < γ) (hℓ : 9 / 11 ≤ ℓ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : 0 ≤ f) (hw : a + b + f ≤ 1 / 4) (hL : L < 7 / 3000) :
    0 < (A - a) * (γ + ℓ * (a + b + f)) - A * f - L := by
  set w := a + b + f with hwdef
  have hw0 : 0 ≤ w := by linarith
  have hid : (A - a) * (γ + ℓ * w) - A * f - L =
      A * (γ - (1 - ℓ) * w + b) + a * (A - γ - ℓ * w) - L := by
    rw [hwdef]; ring
  rw [hid]
  have hδw : (1 - ℓ) * w ≤ 2 / 11 * (1 / 4) :=
    mul_le_mul (by linarith) hw hw0 (by norm_num)
  by_cases hc : 0 ≤ A - γ - ℓ * w
  · have h1 : 0 ≤ a * (A - γ - ℓ * w) := mul_nonneg ha hc
    have h2 : 61 / 200 * (27 / 500 - 1 / 22) ≤ A * (γ - (1 - ℓ) * w) :=
      mul_le_mul hA (by linarith) (by norm_num) (by linarith)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ A by linarith) hb]
  · have hc' : A - γ - ℓ * w < 0 := lt_of_not_ge hc
    have h1 : (w - b) * (A - γ - ℓ * w) ≤ a * (A - γ - ℓ * w) :=
      mul_le_mul_of_nonpos_right (by linarith) hc'.le
    have hid2 : A * (γ - (1 - ℓ) * w + b) + (w - b) * (A - γ - ℓ * w) =
        (A - w + b) * (γ + ℓ * w) := by ring
    have hγw : 27 / 500 ≤ γ + ℓ * w := by nlinarith
    have h2 : 11 / 200 * (27 / 500) ≤ (A - w + b) * (γ + ℓ * w) :=
      mul_le_mul (by linarith) hγw (by norm_num) (by linarith)
    linarith

/-- The `beta = -ell` failed-insertion margin `H(-ell) > 0`, using the exact
root count `2R = A(3A+b-1) + L`. -/
private theorem insertion_margin_neg {A γ ℓ a b f L R : ℝ}
    (hA : 61 / 200 ≤ A) (hA3 : A ≤ 1 / 3) (hγ : 27 / 500 < γ) (hℓ : 9 / 11 ≤ ℓ)
    (hℓ83 : ℓ < 83 / 100)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : 0 ≤ f) (hw : a + b + f ≤ 1 / 4)
    (hL0 : 0 ≤ L) (hL : L < 7 / 3000) (hR : 2 * R = A * (3 * A + b - 1) + L) :
    0 < (A - a) * (γ + ℓ * (a + b + f)) - A * f - L + ℓ * (R + A * f) := by
  have hw0 : 0 ≤ a + b + f := by linarith
  generalize hwdef : a + b + f = w at hw hw0 ⊢
  have hA0 : 0 ≤ A := by linarith
  -- The common negative count term: `ell A (3A-1)/2 ≥ (83/100) A (3A-1)/2`.
  have hcnt : 83 / 100 * (A * (3 * A - 1)) / 2 ≤ ℓ * (A * (3 * A - 1)) / 2 := by
    have hneg : A * (3 * A - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0 (by linarith)
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 83 / 100 - ℓ by linarith) hneg
    linarith
  -- The base bracket `A gamma + (83/100) A(3A-1)/2 - L > 0`.
  have hbase : 1 / 2000 < A * γ + 83 / 100 * (A * (3 * A - 1)) / 2 - L := by
    have hbr : 61 / 200 * (27 / 500 - 83 / 100 * (1 - 3 * (61 / 200)) / 2) ≤
        A * (γ - 83 / 100 * (1 - 3 * A) / 2) :=
      mul_le_mul hA (by linarith) (by norm_num) hA0
    linarith
  have hid : (A - a) * (γ + ℓ * w) - A * f - L + ℓ * (R + A * f) =
      (A - a) * (γ + ℓ * w) - (1 - ℓ) * A * f + ℓ * (A * (3 * A + b - 1)) / 2 -
        (1 - ℓ / 2) * L := by
    have : ℓ * R = ℓ * (A * (3 * A + b - 1)) / 2 + ℓ * L / 2 := by
      linear_combination (ℓ / 2) * hR
    linarith
  rw [hid]
  have hLterm : (1 - ℓ / 2) * L ≤ L := by
    have := mul_nonneg (show 0 ≤ ℓ by linarith) hL0
    linarith
  have hbterm : 0 ≤ ℓ * (A * b) / 2 := by positivity
  have hcount : ℓ * (A * (3 * A + b - 1)) / 2 = ℓ * (A * (3 * A - 1)) / 2 + ℓ * (A * b) / 2 := by
    ring
  rw [hcount]
  -- Eliminate `f = w - a - b`; the result is affine in `a`.
  have hf' : f = w - a - b := by linarith
  rw [hf']
  by_cases hc : 0 ≤ (1 - ℓ) * A - (γ + ℓ * w)
  · -- Slope nonnegative: the `a = 0` endpoint.
    have h1 : 0 ≤ a * ((1 - ℓ) * A - (γ + ℓ * w)) := mul_nonneg ha hc
    have hid0 : (A - a) * (γ + ℓ * w) - (1 - ℓ) * A * (w - a - b) =
        A * γ + A * w * (2 * ℓ - 1) + (1 - ℓ) * A * b +
          a * ((1 - ℓ) * A - (γ + ℓ * w)) := by ring
    rw [hid0]
    have h2 : 0 ≤ A * w * (2 * ℓ - 1) := mul_nonneg (mul_nonneg hA0 hw0) (by linarith)
    have h3 : 0 ≤ (1 - ℓ) * A * b := mul_nonneg (mul_nonneg (by linarith) hA0) hb
    linarith
  · -- Slope negative: the `f = 0` endpoint, then concavity in `w`.
    have hc' : (1 - ℓ) * A - (γ + ℓ * w) < 0 := lt_of_not_ge hc
    have h1 : (w - b) * ((1 - ℓ) * A - (γ + ℓ * w)) ≤ a * ((1 - ℓ) * A - (γ + ℓ * w)) :=
      mul_le_mul_of_nonpos_right (by linarith) hc'.le
    have hid1 : (A - a) * (γ + ℓ * w) - (1 - ℓ) * A * (w - a - b) =
        A * γ + A * w * (2 * ℓ - 1) + (1 - ℓ) * A * b +
          a * ((1 - ℓ) * A - (γ + ℓ * w)) := by ring
    have hid2 : A * γ + A * w * (2 * ℓ - 1) + (1 - ℓ) * A * b +
        (w - b) * ((1 - ℓ) * A - (γ + ℓ * w)) = (A - w + b) * (γ + ℓ * w) := by ring
    rw [hid1]
    have hbw : (A - w) * (γ + ℓ * w) ≤ (A - w + b) * (γ + ℓ * w) := by
      have hγw : 0 ≤ γ + ℓ * w := by
        have := mul_nonneg (show 0 ≤ ℓ by linarith) hw0
        linarith
      have := mul_nonneg hb hγw
      linarith
    -- Concavity: `(A-w)(γ+ℓw) ≥ (1-4w) A γ + 4w (A-1/4)(γ+ℓ/4)`.
    have hconc : (1 - 4 * w) * (A * γ) + 4 * w * ((A - 1 / 4) * (γ + ℓ / 4)) ≤
        (A - w) * (γ + ℓ * w) := by
      have : 0 ≤ ℓ * w * (1 / 4 - w) := mul_nonneg (mul_nonneg (by linarith) hw0) (by linarith)
      linarith
    have hquad : 0 ≤ 3 * A ^ 2 / 2 - A / 4 - 1 / 16 := by
      have := mul_nonneg (show 0 ≤ A - 61 / 200 by linarith)
        (show 0 ≤ 3 / 2 * (A + 61 / 200) - 1 / 4 by linarith)
      linarith
    have hB1 : 1 / 2000 < A * γ + ℓ * (A * (3 * A - 1)) / 2 - L := by linarith
    have hB2 : 1 / 2000 < (A - 1 / 4) * (γ + ℓ / 4) + ℓ * (A * (3 * A - 1)) / 2 - L := by
      have hid3 : (A - 1 / 4) * (γ + ℓ / 4) + ℓ * (A * (3 * A - 1)) / 2 =
          (A - 1 / 4) * γ + ℓ * (3 * A ^ 2 / 2 - A / 4 - 1 / 16) := by ring
      have h4 : 11 / 200 * (27 / 500) ≤ (A - 1 / 4) * γ :=
        mul_le_mul (by linarith) hγ.le (by norm_num) (by linarith)
      have h5 : 0 ≤ ℓ * (3 * A ^ 2 / 2 - A / 4 - 1 / 16) := mul_nonneg (by linarith) hquad
      linarith
    have hm1 : 0 ≤ (1 - 4 * w) * (A * γ + ℓ * (A * (3 * A - 1)) / 2 - L - 1 / 2000) :=
      mul_nonneg (by linarith) (by linarith)
    have hm2 : 0 ≤ 4 * w *
        ((A - 1 / 4) * (γ + ℓ / 4) + ℓ * (A * (3 * A - 1)) / 2 - L - 1 / 2000) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- The failed-insertion margin at a private hole point. For a HIGH hole atom
of mass `a` (or dust, `a = 0`) with additional LOW nonneighbors of mass `f`,
`w = a + b + f <= 1/4`, the insertion inequality
`(R + A f) beta ≥ (A - a)(gamma + ell w) - A f - L` is impossible for every
`-ell <= beta <= 0`, given `61/200 <= A <= 1/3`, `gamma > 27/500`,
`9/11 <= ell < 83/100`, `0 <= L < 7/3000` and the exact root count. -/
theorem failed_insertion_margin {A γ ℓ a b f L R β : ℝ}
    (hA : 61 / 200 ≤ A) (hA3 : A ≤ 1 / 3) (hγ : 27 / 500 < γ) (hℓ : 9 / 11 ≤ ℓ)
    (hℓ83 : ℓ < 83 / 100)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : 0 ≤ f) (hw : a + b + f ≤ 1 / 4)
    (hL0 : 0 ≤ L) (hL : L < 7 / 3000) (hR : 2 * R = A * (3 * A + b - 1) + L)
    (hβ : -ℓ ≤ β) (hβ0 : β ≤ 0) :
    (R + A * f) * β < (A - a) * (γ + ℓ * (a + b + f)) - A * f - L := by
  have h0 := insertion_margin_zero hA hγ hℓ ha hb hf hw hL
  have h1 := insertion_margin_neg hA hA3 hγ hℓ hℓ83 ha hb hf hw hL0 hL hR
  by_cases hs : 0 ≤ R + A * f
  · have : (R + A * f) * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hβ0
    linarith
  · have hs' : R + A * f < 0 := lt_of_not_ge hs
    have : (R + A * f) * (β + ℓ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hs'.le (by linarith)
    nlinarith

end Erdos1017.MiddlePrivateSoleSourceScalar
