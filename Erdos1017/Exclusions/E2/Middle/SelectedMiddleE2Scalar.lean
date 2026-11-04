module

public import Erdos1017.Exclusions.Common.E2.EmptySatE2Scalar

/-!
# Scalar facts on the middle `E₂` range

On the middle range the multiplier lies strictly between the upper-`E₂` guard
and the lower-`E₂` boundary value, the missing mass is below one third, the
two-head value exceeds one eighth, and the one-center extra-hole location is
impossible (`not_extra_hole`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleE2Parameter

open LowerE2Scalar

/-- The own middle-E2 multiplier lies strictly between the upper-E2 guard
and its lower-E2 boundary value. -/
theorem multiplier_mem {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    multiplier q ∈ Ioo (9 / 11 : ℝ) (19 / 21) := by
  have hden : 0 < 2 + q := by linarith [hq.1]
  unfold multiplier
  constructor
  · rw [lt_div_iff₀ hden]
    linarith [hq.2]
  · rw [div_lt_iff₀ hden]
    linarith [hq.1]

/-- On the middle range the stationary missing mass is below one third,
so the contact density exceeds one third. -/
theorem missingMass_lt_third {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    missingMass q < 1 / 3 := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have h2 : (1 / 10 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1.le 2
  have h3 : q ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := pow_le_pow_left₀ hq0 hq.2.le 3
  have h4 : q ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hq0 hq.2.le 4
  have hpoly : 0 < -4 + 52 * q + 201 * q ^ 2 - 56 * q ^ 3 - 31 * q ^ 4 := by
    norm_num at h2 h3 h4
    linarith [hq.1]
  have hid : 8 * denominator q ^ 2 - 3 * ((q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2)) =
      -4 + 52 * q + 201 * q ^ 2 - 56 * q ^ 3 - 31 * q ^ 4 := by
    unfold denominator
    ring
  unfold missingMass
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- The stationary two-head value exceeds one eighth throughout the
middle range. -/
theorem twoHeadValue_gt_eighth {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    1 / 8 < Benchmark.twoHeadValue ((q + 2) / 3) := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hq2 : q ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hq0 hq.2.le 2
  have hfactor : 0 ≤ 7 * q ^ 3 - (133 / 5) * q ^ 2 + (242 / 25) * q + 1242 / 125 := by
    have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq0 3
    nlinarith only [hq0, hq2, hq3]
  have hprod := mul_nonneg (show 0 ≤ 1 / 5 - q by linarith only [hq.2]) hfactor
  have hid : 4 + 20 * q + 87 * q ^ 2 + 56 * q ^ 3 - 5 * q ^ 4 -
      2 * denominator q ^ 2 = 8 / 625 + (1 / 5 - q) *
        (7 * q ^ 3 - (133 / 5) * q ^ 2 + (242 / 25) * q + 1242 / 125) := by
    unfold denominator
    ring
  rw [Erdos1017.EmptySatE2.contact_value_eq hq0]
  apply (lt_div_iff₀ (show 0 < 16 * denominator q ^ 2 by positivity)).mpr
  nlinarith only [hid, hprod]

private theorem gapFloor_ge {q : ℝ} (g : ℝ) (hq0 : 0 ≤ q)
    (hpoly : 0 ≤ q * (1 + 2 * q) - 2 * g * denominator q) : g ≤ gapFloor q := by
  have hR := denominator_pos hq0
  unfold gapFloor
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The one-center extra-hole location is impossible on the middle range.
The inputs are the actual recovered-height credit, the original forward
reserve and the flat head row with the outside mass bound. -/
theorem not_extra_hole {q ell gamma c A t : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hell : ell = multiplier q) (hgamma : gapFloor q < gamma)
    (hc : Benchmark.twoHeadValue ((q + 2) / 3) < c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hct : c ≤ t ^ 2)
    (hreserve : gamma ≤ (2 - ell) * A ^ 2)
    (hrow : (1 + ell) * (A + t) ≤ 1 - gamma) : False := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hl := multiplier_mem hq
  rw [← hell] at hl
  have hB := twoHeadValue_gt_eighth hq
  have htlow : 353 / 1000 < t := by
    by_contra h
    have h2 := pow_le_pow_left₀ ht (le_of_not_gt h) 2
    norm_num at h2
    linarith
  have hscale : (2 - ell) * A ^ 2 ≤ 13 / 11 * A ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hl.1]) (sq_nonneg A)
  have hlow (g : ℝ) (hg : g ≤ gapFloor q) (a : ℝ) (ha : 0 ≤ a)
      (hag : 13 / 11 * a ^ 2 < g) : a < A := by
    have hA2 : a ^ 2 < A ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 hA hA2
  have hfinal (ell0 a : ℝ) (hell0 : ell0 ≤ ell) (ha : a < A) (ha0 : 0 ≤ a) (hl0 : 0 ≤ ell0) :
      (1 + ell0) * (a + 353 / 1000) ≤ 1 - gamma :=
    (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)).trans hrow
  by_cases hsplit : q ≤ 3 / 20
  · have hg := gapFloor_ge (7 / 200) hq0
      (by unfold denominator; nlinarith [hq.1])
    have hell' : 86 / 100 ≤ ell := by
      rw [hell]
      unfold multiplier
      rw [le_div_iff₀ (by linarith)]
      linarith
    have h := hfinal _ _ hell' (hlow _ hg (172 / 1000) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
    linarith
  · have hg := gapFloor_ge (46 / 1000) hq0
      (by unfold denominator; nlinarith [hq.1])
    have h := hfinal _ _ hl.1.le (hlow _ hg (197 / 1000) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
    linarith

end Erdos1017.MiddleE2Parameter
