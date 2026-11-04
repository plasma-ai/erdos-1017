module

public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards

/-!
# Scalar bounds for the two-center `E₂` case

The two-center intercept guard holds on the whole scalar interval, a recovered
head's square budget and positive-body trace contradict the `E₂` certificate at
both endpoints (`not_two_center_head_trace`), and reverse and forward square
budgets make the entire outside mass smaller than the original peak.
-/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators unitInterval

namespace Erdos1017.LowerE2Scalar

private def headPolynomial (q : ℝ) : ℝ :=
  -80 * q ^ 8 - 456 * q ^ 7 - 793 * q ^ 6 + 630 * q ^ 5 + 2173 * q ^ 4 +
    674 * q ^ 3 - 349 * q ^ 2 + 68 * q - 4

private theorem headPolynomial_pos {q : ℝ} (hq : q ∈ Icc (1 / 10 : ℝ) (2 / 9)) :
    0 < headPolynomial q := by
  let x : I := ⟨(90 * q - 9) / 11, by constructor <;> nlinarith [hq.1, hq.2]⟩
  let c : Fin 9 → ℝ := ![1033803 / 5000000, 12500151 / 20000000,
    87122153 / 84000000, 1017225463 / 680400000, 9451407893 / 4592700000,
    923450911 / 330674400, 1871653957 / 496011600, 243053357 / 47829690,
    292950256 / 43046721]
  have hc : ∀ i, (1 / 100 : ℝ) ≤ c i := by intro i; fin_cases i <;> norm_num [c]
  have hp : 0 < ∑ i, c i * bernstein 8 i x := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_right (hc i) (bernstein_nonneg (n := 8) (ν := i) (x := x)))
    rw [← Finset.mul_sum, bernstein.probability, mul_one] at hh
    linarith
  convert hp using 1
  norm_num [headPolynomial, c, Fin.sum_univ_succ, bernstein_apply, Nat.choose, x]
  ring

/-- The two-center intercept guard holds on the whole scalar
interval, without asserting that the E2 family is active there. -/
theorem two_center_gapFloor_gt_quarter {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) :
    (1 - multiplier q) / 4 < gapFloor q := by
  have hR := (denominator_pos hq.1.le).ne'
  have hq2 : 2 + q ≠ 0 := by linarith [hq.1]
  have hq2' : q + 2 ≠ 0 := by linarith [hq.1]
  have hid : gapFloor q - (1 - multiplier q) / 4 =
      q * (q - 1) ^ 2 / (2 * denominator q * (q + 2)) := by
    unfold gapFloor multiplier
    field_simp [hq2]
    unfold denominator
    field_simp [hq2, hq2']
    ring
  rw [← sub_pos, hid]
  apply div_pos
  · exact mul_pos hq.1 (sq_pos_of_ne_zero (by linarith [hq.2]))
  · exact mul_pos (mul_pos (by norm_num) (denominator_pos hq.1.le)) (by linarith [hq.1])

private theorem head_certificate {q : ℝ} (hq : q ∈ Icc (1 / 10 : ℝ) (2 / 9)) :
    let X := gapFloor q / (2 * (1 - multiplier q))
    0 < 4 * (gapFloor q) ^ 2 * X -
      (2 * missingMass q - 3 * X - (gapFloor q) ^ 2) ^ 2 := by
  have hqpos : 0 < q := by linarith [hq.1]
  have hR := (denominator_pos hqpos.le).ne'
  have hq0 := hqpos.ne'
  have hq2 : 2 + q ≠ 0 := by linarith
  have hd : 1 - multiplier q ≠ 0 := ne_of_gt (sub_pos.mpr
    (contact_multiplier_mem ⟨hqpos, hq.2⟩).2)
  dsimp
  have hid : 4 * (gapFloor q) ^ 2 * (gapFloor q / (2 * (1 - multiplier q))) -
      (2 * missingMass q - 3 * (gapFloor q / (2 * (1 - multiplier q))) -
        (gapFloor q) ^ 2) ^ 2 = headPolynomial q / (64 * denominator q ^ 4) := by
    have hX : gapFloor q / (2 * (1 - multiplier q)) =
        (q + 2) * (2 * q + 1) / (8 * denominator q) := by
      unfold gapFloor multiplier
      field_simp [hq0, hR, hq2]
      ring
    rw [hX]
    unfold gapFloor missingMass
    field_simp [hR]
    unfold headPolynomial denominator
    ring
  rw [hid]
  exact div_pos (headPolynomial_pos hq) (by positivity)

/-- A recovered head's actual square budget and positive-body trace
contradict the exact E2 certificate, including both scalar endpoints. -/
theorem not_two_center_head_trace {q A gamma : ℝ}
    (hq : q ∈ Icc (1 / 10 : ℝ) (2 / 9)) (hA : 0 ≤ A)
    (hgamma : gapFloor q ≤ gamma)
    (hbudget : gamma ≤ 2 * (1 - multiplier q) * A ^ 2)
    (htrace : 3 * A ^ 2 + 2 * A * gamma + gamma ^ 2 ≤ 2 * missingMass q) : False := by
  have hqpos : 0 < q := by linarith [hq.1]
  have hg := contact_gapFloor_pos hqpos
  have hd : 0 < 2 * (1 - multiplier q) := by
    have hh := (contact_multiplier_mem ⟨hqpos, hq.2⟩).2
    linarith
  let X := gapFloor q / (2 * (1 - multiplier q))
  let V := 2 * missingMass q - 3 * X - (gapFloor q) ^ 2
  have hX : X ≤ A ^ 2 := (div_le_iff₀ hd).mpr (by nlinarith)
  have hgg : (gapFloor q) ^ 2 ≤ gamma ^ 2 := by nlinarith
  have hAg := mul_nonneg hA (sub_nonneg.mpr hgamma)
  have hV : 2 * A * gapFloor q ≤ V := by dsimp [V]; nlinarith
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  have hs : 4 * A ^ 2 * (gapFloor q) ^ 2 ≤ V ^ 2 := by
    have hh := mul_self_le_mul_self (show 0 ≤ 2 * A * gapFloor q by positivity) hV
    nlinarith only [hh]
  have hprod := mul_le_mul_of_nonneg_right hX (sq_nonneg (gapFloor q))
  have hc := head_certificate hq
  change 0 < 4 * (gapFloor q) ^ 2 * X - V ^ 2 at hc
  nlinarith

private theorem outside_certificate {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) :
    let X := gapFloor q / (2 * (1 - multiplier q))
    let Y := gapFloor q / (2 - multiplier q)
    0 < 16 * X * Y - (1 - 4 * X - Y) ^ 2 := by
  have hR := (denominator_pos hq.1.le).ne'
  have hq0 := hq.1.ne'
  have hq2 : 2 + q ≠ 0 := by linarith [hq.1]
  have hq2' : q + 2 ≠ 0 := by linarith [hq.1]
  have hq3 : 3 * q + 2 ≠ 0 := by linarith [hq.1]
  have hq3' : 2 + q * 3 ≠ 0 := by linarith [hq.1]
  have hq9 : 4 + q * 12 + q ^ 2 * 9 ≠ 0 := by nlinarith [hq.1, sq_nonneg q]
  have h1 : 11 * q ^ 2 + 2 * q - 4 < 0 := by nlinarith [hq.1, hq.2]
  have hq3bound : q ^ 3 ≤ (2 / 9 : ℝ) ^ 3 := pow_le_pow_left₀ hq.1.le hq.2 3
  have h2 : q ^ 3 + 8 * q ^ 2 + 2 * q - 2 < 0 := by nlinarith [hq.1, hq.2]
  dsimp
  have hid :
      16 * (gapFloor q / (2 * (1 - multiplier q))) * (gapFloor q / (2 - multiplier q)) -
        (1 - 4 * (gapFloor q / (2 * (1 - multiplier q))) -
          (gapFloor q / (2 - multiplier q))) ^ 2 =
      q * (11 * q ^ 2 + 2 * q - 4) * (q ^ 3 + 8 * q ^ 2 + 2 * q - 2) /
        ((3 * q + 2) ^ 2 * denominator q ^ 2) := by
    have hX : gapFloor q / (2 * (1 - multiplier q)) =
        (q + 2) * (2 * q + 1) / (8 * denominator q) := by
      unfold gapFloor multiplier
      field_simp [hq0, hR, hq2]
      ring
    have hY : gapFloor q / (2 - multiplier q) =
        q * (2 * q + 1) * (q + 2) / (2 * denominator q * (3 * q + 2)) := by
      unfold gapFloor multiplier
      field_simp [hR, hq2, hq3]
      ring
    rw [hX, hY]
    field_simp [hR, hq3]
    unfold denominator
    ring_nf
    field_simp [hq3', hq9]
    ring
  rw [hid]
  exact div_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hq.1 h1) h2) (by positivity)

/-- Actual reverse and forward square budgets make the entire outside
mass smaller than the original peak. No radical comparison is assumed. -/
theorem two_center_outside_lt_peak {q A t gamma : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) (2 / 9)) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hgamma : gapFloor q ≤ gamma)
    (hreverse : gamma ≤ 2 * (1 - multiplier q) * t ^ 2)
    (hforward : gamma ≤ (2 - multiplier q) * A ^ 2) : 1 - 2 * t < A := by
  have hell := contact_multiplier_mem hq
  have hd : 0 < 2 * (1 - multiplier q) := by linarith [hell.2]
  have he : 0 < 2 - multiplier q := by linarith [hell.2]
  let X := gapFloor q / (2 * (1 - multiplier q))
  let Y := gapFloor q / (2 - multiplier q)
  have hX0 : 0 ≤ X := (div_nonneg (contact_gapFloor_pos hq.1).le hd.le)
  have hX : X ≤ t ^ 2 := (div_le_iff₀ hd).mpr (by nlinarith)
  have hY : Y ≤ A ^ 2 := (div_le_iff₀ he).mpr (by nlinarith)
  by_contra hn
  have hsum : 2 * t + A ≤ 1 := by linarith
  have hsq : (2 * t + A) ^ 2 ≤ 1 := by nlinarith
  let D := 1 - 4 * X - Y
  have hD : 4 * t * A ≤ D := by dsimp [D]; nlinarith
  have hs : 16 * t ^ 2 * A ^ 2 ≤ D ^ 2 := by
    have hh := mul_self_le_mul_self (show 0 ≤ 4 * t * A by positivity) hD
    nlinarith only [hh]
  have hprod := mul_le_mul hX hY (div_nonneg (contact_gapFloor_pos hq.1).le he.le)
    (sq_nonneg t)
  have hc := outside_certificate hq
  change 0 < 16 * X * Y - D ^ 2 at hc
  nlinarith

end Erdos1017.LowerE2Scalar
