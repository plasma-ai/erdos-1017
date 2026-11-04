module

public import Erdos1017.Exclusions.E2.Upper.UpperE2ParameterGuards

/-!
# Scalar contradictions for the upper `E₂` private case

The private-body trace pays the triangle margin on the upper-`E₂` interval, the
small-private-atom unsaturated demand contradicts an exact completed-square certificate, a
large private atom violates the original covariance bound in the unsaturated
case, and the saturated whole-hole bill forces a covariance contradiction for
every private mass.
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.UpperE2PrivateScalar

/-- The actual private-body trace pays the triangle margin on the upper-E2 interval. -/
theorem triangle_margin {q A b k γ : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hA : 1 / 3 < A) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hγ : LowerE2Scalar.gapFloor q < γ)
    (hbody : (A + b) ^ 2 ≤ LowerE2Scalar.missingMass q)
    (htrace : b ≤ γ →
      2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤
        2 * LowerE2Scalar.missingMass q) :
    2 * (1 - LowerE2Scalar.multiplier q) * A < 3 * γ := by
  have hell := UpperE2Parameter.multiplier_mem hq
  have hh0 := UpperE2Parameter.missingMass_mem hq
  have hh : LowerE2Scalar.missingMass q < 59 / 250 :=
    lt_of_le_of_lt hh0.2 (by norm_num)
  have hg := UpperE2Parameter.gapFloor_ge hq
  have hγlower : 7 / 122 < γ := hg.trans_lt hγ
  have hα : A + b < 243 / 500 := by
    have hαpos : 0 < A + b := by linarith
    nlinarith [hbody, hh]
  have hAupper : A < 43 / 100 := by
    by_cases hbg : b ≤ γ
    · have ht := htrace hbg
      have hαsq : A ^ 2 ≤ (A + b) ^ 2 := by nlinarith
      have hβsq : A ^ 2 ≤ (A + γ - b) ^ 2 := by nlinarith
      have hbk : 0 ≤ b * k := mul_nonneg hb hk
      have hA2 : A < 2 / 5 := by nlinarith [ht, hαsq, hβsq, hh]
      linarith
    · have hbγ : γ < b := lt_of_not_ge hbg
      linarith [hα, hγlower]
  have hδ : 0 < 1 - LowerE2Scalar.multiplier q ∧
      1 - LowerE2Scalar.multiplier q < 1 / 5 := by
    constructor <;> linarith [hell.1, hell.2]
  have hmul := mul_lt_mul_of_pos_right hδ.2 (show 0 < A by linarith [hA])
  have hmul2 : (1 / 5 : ℝ) * A < (1 / 5) * (43 / 100) := by
    gcongr
  nlinarith [hmul, hmul2, hγlower]

private theorem r7_poly_pos {q : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000)) :
    0 < 435 - 1920 * q - 1629 * q ^ 2 + 7764 * q ^ 3 - 2706 * q ^ 4 := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hq2 : q ^ 2 ≤ (213 / 1000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hq0 hq.2 2
  have hq3 : (1 / 5 : ℝ) ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hq.1 3
  have hq4 : q ^ 4 ≤ (213 / 1000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hq0 hq.2 4
  norm_num at hq2 hq3 hq4
  linarith [hq.2]

private theorem r7_identity {q : ℝ} (hq : 0 ≤ q) :
    let a0 := 2 / 3 + LowerE2Scalar.gapFloor q
    a0 ^ 2 - 2 * LowerE2Scalar.missingMass q +
      14 * Benchmark.twoHeadValue ((q + 2) / 3) -
      (7 + 2 * a0) ^ 2 / 40 =
      (435 - 1920 * q - 1629 * q ^ 2 + 7764 * q ^ 3 - 2706 * q ^ 4) /
        (360 * LowerE2Scalar.denominator q ^ 2) := by
  dsimp
  have hR := ne_of_gt (LowerE2Scalar.denominator_pos hq)
  have h2 : q + 2 ≠ 0 := by linarith
  have hB := LowerE2Scalar.gapFloor_eq_twoHeadValue hq
  rw [show Benchmark.twoHeadValue ((q + 2) / 3) =
    (LowerE2Scalar.gapFloor q +
      LowerE2Scalar.multiplier q * LowerE2Scalar.missingMass q) / 2 by linarith]
  unfold LowerE2Scalar.gapFloor LowerE2Scalar.multiplier
    LowerE2Scalar.missingMass
  field_simp
  simp only [LowerE2Scalar.denominator]
  ring

/-- The small-private-atom unsaturated demand contradicts an exact completed-square
certificate (`r7_identity`, `r7_poly_pos`). -/
theorem unsaturated_small_b_false {q A b k γ c : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hA : 1 / 3 < A) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hγeq : γ = 2 * c - LowerE2Scalar.multiplier q * LowerE2Scalar.missingMass q)
    (hc : Benchmark.twoHeadValue ((q + 2) / 3) < c)
    (hbody : (A + b) ^ 2 ≤ LowerE2Scalar.missingMass q)
    (hbg : b ≤ γ)
    (htrace : 2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤
      2 * LowerE2Scalar.missingMass q)
    (hdemand : 2 * c ≤ (A + b) * (1 - A - b) - b * k) : False := by
  have hγ : LowerE2Scalar.gapFloor q < γ := by
    have hq0 : 0 ≤ q := by linarith [hq.1]
    linarith [LowerE2Scalar.gapFloor_eq_twoHeadValue hq0]
  let α := A + b
  let a0 := 2 / 3 + LowerE2Scalar.gapFloor q
  let h := LowerE2Scalar.missingMass q
  let B := Benchmark.twoHeadValue ((q + 2) / 3)
  have hαpos : 0 < α := by dsimp [α]; linarith
  have hαlt : α < 243 / 500 := by
    have hh := UpperE2Parameter.missingMass_mem hq
    have hh' : h < 59 / 250 := lt_of_le_of_lt hh.2 (by norm_num)
    dsimp [α, h] at *
    nlinarith [hbody]
  have hβpos : 0 < A + γ - b := by
    have hg := UpperE2Parameter.gapFloor_ge hq
    have hγlower : 7 / 122 < γ := hg.trans_lt hγ
    dsimp [α] at hαlt
    linarith
  have ha0pos : 0 < a0 - α := by
    have hG := UpperE2Parameter.gapFloor_ge hq
    dsimp [a0]
    linarith
  have hβgt : a0 - α < A + γ - b := by
    dsimp [a0, α]
    linarith [hA, hγ]
  have hsq : (a0 - α) ^ 2 < (A + γ - b) ^ 2 := by nlinarith
  have hbk : 0 ≤ b * k := mul_nonneg hb hk
  have hT : 2 * α ^ 2 + (a0 - α) ^ 2 - 2 * h < 0 := by
    dsimp [α, h] at *
    nlinarith [htrace, hsq, hbk]
  have hL : 0 < α * (1 - α) - 2 * B := by
    dsimp [α, B] at *
    nlinarith [hdemand, hc, hbk]
  have hr7 := r7_identity (show 0 ≤ q by linarith [hq.1])
  have hr7pos : 0 < a0 ^ 2 - 2 * h + 14 * B - (7 + 2 * a0) ^ 2 / 40 := by
    dsimp [a0, h, B]
    rw [hr7]
    exact div_pos (r7_poly_pos hq) (mul_pos (by norm_num)
      (pow_pos (LowerE2Scalar.denominator_pos (by linarith [hq.1])) 2))
  have hcomplete :
      2 * α ^ 2 + (a0 - α) ^ 2 - 2 * h - 7 * (α * (1 - α) - 2 * B) =
      10 * (α - (7 + 2 * a0) / 20) ^ 2 +
        (a0 ^ 2 - 2 * h + 14 * B - (7 + 2 * a0) ^ 2 / 40) := by ring
  nlinarith [sq_nonneg (α - (7 + 2 * a0) / 20)]

set_option maxHeartbeats 2000000 in
/-- A large private atom violates the original covariance bound in the unsaturated case. -/
theorem unsaturated_large_b_false {q A b k γ c : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hA : 1 / 3 < A) (hb : γ < b) (hk : 0 < k)
    (hγeq : γ = 2 * c - LowerE2Scalar.multiplier q * LowerE2Scalar.missingMass q)
    (hc : Benchmark.twoHeadValue ((q + 2) / 3) < c)
    (hbody : (A + b) ^ 2 ≤ LowerE2Scalar.missingMass q)
    (hdemand : 2 * c ≤ (A + b) * (1 - A - b) - b * k)
    (hcov : (A + b + k - LowerE2Scalar.missingMass q) ^ 2 <
      2 * (γ + LowerE2Scalar.multiplier q) * k * (A + k)) : False := by
  let α := A + b
  let h := LowerE2Scalar.missingMass q
  let ell := LowerE2Scalar.multiplier q
  let ν := γ + ell
  have hell := UpperE2Parameter.multiplier_mem hq
  have hh := UpperE2Parameter.missingMass_mem hq
  have hG := UpperE2Parameter.gapFloor_ge hq
  have hB := UpperE2Parameter.twoHeadValue_gt hq
  have hγ : LowerE2Scalar.gapFloor q < γ := by
    have hq0 : 0 ≤ q := by linarith [hq.1]
    linarith [LowerE2Scalar.gapFloor_eq_twoHeadValue hq0]
  have hγ57 : 57 / 1000 < γ := by linarith [hG]
  have hαpos : 0 < α := by dsimp [α]; linarith [hA, hb, hγ57]
  have hαlt : α < 243 / 500 := by
    have hh' : h < 59 / 250 := lt_of_le_of_lt hh.2 (by norm_num)
    dsimp [α, h] at *
    nlinarith [hbody]
  have hαhalf : α < 1 / 2 := by linarith
  have hα109 : 109 / 250 < α := by
    have hprod : α * (1 - α) ≤ 1 / 4 := by nlinarith [sq_nonneg (α - 1 / 2)]
    have hc123 : 123 / 1000 < c := lt_trans hB hc
    dsimp [α] at *
    nlinarith [hdemand]
  have hbk : b * k < 1 / 250 := by
    have hprod : α * (1 - α) ≤ 1 / 4 := by nlinarith [sq_nonneg (α - 1 / 2)]
    have hc123 : 123 / 1000 < c := lt_trans hB hc
    dsimp [α] at *
    nlinarith [hdemand]
  have hk4 : k < 4 / 57 := by
    have hblt : 57 / 1000 < b := lt_trans hγ57 hb
    nlinarith [hbk]
  have hν : ν < 22 / 25 := by
    have hprod : α * (1 - α) ≤ 1 / 4 := by nlinarith [sq_nonneg (α - 1 / 2)]
    have hhbelow : 23 / 100 < h := hh.1
    have hhh : 0 < 1 - h := by linarith [hh.2]
    have hellbound : ell * (1 - h) ≤ (9 / 11) * (1 - h) :=
      mul_le_mul_of_nonneg_right hell.2 (le_of_lt hhh)
    dsimp [ν, ell, h, α] at *
    nlinarith [hdemand, hellbound]
  have hD : 1 / 5 + k < α + k - h := by
    have hhupper : h < 59 / 250 := lt_of_le_of_lt hh.2 (by norm_num)
    dsimp [α, h] at *
    linarith
  have hAk : 0 < A + k ∧ A + k < 1 / 2 + k := by
    dsimp [α] at hαhalf
    constructor <;> linarith [hb, hγ57]
  have hcovupper :
      2 * ν * k * (A + k) < (44 / 25) * k * (1 / 2 + k) := by
    have h1 : 2 * ν * k * (A + k) < (44 / 25) * k * (A + k) := by
      have hkp : 0 < k * (A + k) := mul_pos hk hAk.1
      nlinarith [mul_lt_mul_of_pos_right hν hkp]
    have h2 : (44 / 25) * k * (A + k) < (44 / 25) * k * (1 / 2 + k) := by
      have hkp : 0 < (44 / 25 : ℝ) * k := mul_pos (by norm_num) hk
      nlinarith [mul_lt_mul_of_pos_left hAk.2 hkp]
    linarith
  have hpoly : (44 / 25) * k * (1 / 2 + k) < (1 / 5 + k) ^ 2 := by
    have hk0 : 0 ≤ k := le_of_lt hk
    nlinarith [hk4, mul_nonneg hk0 (show 0 ≤ 4 / 57 - k by linarith [hk4])]
  dsimp [α, h, ell, ν] at *
  nlinarith [sq_nonneg (A + b + k - LowerE2Scalar.missingMass q)]

set_option maxHeartbeats 2000000 in
/-- The saturated whole-hole bill forces a covariance contradiction for every private mass. -/
theorem saturated_false {q A b k γ c : ℝ}
    (hq : q ∈ Icc (1 / 5 : ℝ) (213 / 1000))
    (hA : 1 / 3 < A) (hb : 0 < b) (hk : 0 < k)
    (hAk : k < A)
    (hγeq : γ = 2 * c - LowerE2Scalar.multiplier q * LowerE2Scalar.missingMass q)
    (hc : Benchmark.twoHeadValue ((q + 2) / 3) < c)
    (hDelta : 0 < 1 - LowerE2Scalar.multiplier q - 2 * γ)
    (hV : 0 < 1 - 2 * LowerE2Scalar.missingMass q - A + k)
    (hbill : k + 2 * (2 * c - LowerE2Scalar.missingMass q) +
        ((A - k) * k / (1 - 2 * LowerE2Scalar.missingMass q - A + k)) *
          (1 - LowerE2Scalar.multiplier q - 2 * γ) <
      (1 - LowerE2Scalar.multiplier q) *
        (1 - 2 * LowerE2Scalar.missingMass q - A))
    (hcov : (A + b + k - LowerE2Scalar.missingMass q) ^ 2 <
      2 * (γ + LowerE2Scalar.multiplier q) * k * (A + k)) : False := by
  let h := LowerE2Scalar.missingMass q
  let ell := LowerE2Scalar.multiplier q
  let g := LowerE2Scalar.gapFloor q
  let B := Benchmark.twoHeadValue ((q + 2) / 3)
  let δ := 1 - ell
  let ν := γ + ell
  let s := A + k
  let a := 1 / 3 + k
  have hell := UpperE2Parameter.multiplier_mem hq
  have hh := UpperE2Parameter.missingMass_mem hq
  have hg := UpperE2Parameter.gapFloor_ge hq
  have hBidentity : 2 * B = g + ell * h := by
    dsimp [B, g, ell, h]
    have hq0 : 0 ≤ q := by linarith [hq.1]
    linarith [LowerE2Scalar.gapFloor_eq_twoHeadValue hq0]
  have hcorr : 0 < ((A - k) * k /
      (1 - 2 * h - A + k)) * (1 - ell - 2 * γ) := by
    apply mul_pos
    · exact div_pos (mul_pos (by linarith [hAk]) hk) hV
    · exact hDelta
  have hk17 : k < 17 / 915 := by
    have hδ : δ < 1 / 5 := by dsimp [δ, ell]; linarith [hell.1]
    have hg7 : 7 / 122 ≤ g := hg
    dsimp [δ, ell, g, h] at *
    nlinarith [hbill, hcorr, hBidentity, hc, hA]
  have hk50 : k < 1 / 50 := by linarith [hk17]
  have hhupper : h < 59 / 250 := lt_of_le_of_lt hh.2 (by norm_num)
  have hν : 2 * ν < 20 / 11 := by
    dsimp [ν, ell] at *
    linarith [hDelta, hell.2]
  have hs : a < s := by dsimp [a, s]; linarith [hA]
  have ha : 0 < a := by dsimp [a]; linarith [hk]
  have hhsa : h < a := by dsimp [a]; linarith [hhupper, hk]
  have hsa : 0 < s := lt_trans ha hs
  have hsminus : 0 < s - h := by linarith
  have hD : s - h < A + b + k - h := by dsimp [s]; linarith [hb]
  have hDsq : (s - h) ^ 2 < (A + b + k - h) ^ 2 := by nlinarith
  have hcov' : (s - h) ^ 2 < (20 / 11) * k * s := by
    have hνk : 2 * ν * k * s < (20 / 11) * k * s := by
      have hks : 0 < k * s := mul_pos hk hsa
      nlinarith [mul_lt_mul_of_pos_right hν hks]
    dsimp [s, ν, ell, h] at *
    nlinarith [hcov, hDsq]
  have hmonotone : (a - h) ^ 2 * s < (s - h) ^ 2 * a := by
    have hsa2 : h ^ 2 < s * a := by nlinarith [mul_pos (sub_pos.mpr hhsa) (sub_pos.mpr (lt_trans hhsa hs))]
    calc
      (a - h) ^ 2 * s = (s - h) ^ 2 * a - (s - a) * (s * a - h ^ 2) := by ring
      _ < (s - h) ^ 2 * a := by nlinarith [hs, hsa2]
  have hratio : (a - h) ^ 2 < (20 / 11) * k * a := by
    have hcovmul := mul_lt_mul_of_pos_right hcov' ha
    have hratio2 : (a - h) ^ 2 * s < (20 / 11) * k * s * a := by
      nlinarith [hmonotone, hcovmul]
    nlinarith [hratio2, hsa]
  have hamin : 73 / 750 + k < a - h := by dsimp [a]; linarith [hhupper]
  have haminpos : 0 < 73 / 750 + k := by linarith [hk]
  have hamin_sq : (73 / 750 + k) ^ 2 < (a - h) ^ 2 := by nlinarith
  have hpoly : (20 / 11) * k * (1 / 3 + k) < (73 / 750 + k) ^ 2 := by
    have hk0 : 0 ≤ k := le_of_lt hk
    nlinarith [hk50, mul_nonneg hk0 (show 0 ≤ 1 / 50 - k by linarith [hk50])]
  dsimp [a] at hratio
  nlinarith [hpoly, hamin_sq, hratio]

end Erdos1017.UpperE2PrivateScalar
