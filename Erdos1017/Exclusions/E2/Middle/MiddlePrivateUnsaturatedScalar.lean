module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates

/-!
# Scalar facts for the middle private unsaturated case

On the no-saturation range the own multiplier is below `83/100`, the shifted-row
floor exceeds `27/500` and the whole-law surplus `d - 3B` is below `1/100`;
these give the common parent-phase contradiction for one positive secondary
source row of mass `a < 4/25` (`phase_false`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddlePrivateUnsaturatedScalar

open LowerE2Scalar

/-- On the no-saturation range the own multiplier is below `83/100`. -/
theorem multiplier_lt {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    multiplier q < 83 / 100 := by
  unfold multiplier
  rw [div_lt_iff₀ (by linarith [hq.1])]
  linarith [hq.1]

/-- On the no-saturation range the shifted-row floor exceeds `27/500`. -/
theorem gapFloor_gt {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    27 / 500 < gapFloor q := by
  have hR := denominator_pos (by linarith [hq.1] : (0 : ℝ) ≤ q)
  unfold gapFloor
  rw [lt_div_iff₀ (by positivity)]
  unfold denominator
  nlinarith [hq.1, hq.2]

/-- The whole-law surplus `d - 3B` is below `1/100` on the no-saturation range. -/
theorem surplus_lt {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    (1 - missingMass q) / 2 - 3 * Benchmark.twoHeadValue ((q + 2) / 3) < 1 / 100 := by
  have hq0 : (0 : ℝ) ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hid := pairFloor_eq_twoHeadValue hq0
  have h2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  have h3 : (187 / 1000 : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq.1 3
  have h3' : q ^ 3 ≤ (1 / 5 : ℝ) ^ 3 := pow_le_pow_left₀ hq0 hq.2 3
  have h4 : q ^ 4 ≤ (1 / 5 : ℝ) ^ 4 := pow_le_pow_left₀ hq0 hq.2 4
  have hpoly : -100 * pairNumerator q < 8 * denominator q ^ 2 := by
    unfold pairNumerator denominator
    norm_num at h2 h3 h3' h4
    nlinarith [hq.1, hq.2]
  have hfloor : -(2 * pairFloor q) < 1 / 100 := by
    unfold pairFloor
    rw [neg_lt, mul_div_assoc', lt_div_iff₀ (by positivity)]
    linarith
  linarith

/-- The common parent-phase contradiction for one positive secondary source
row of mass `a < 4/25` (`a = 0` for genuine source dust). The inputs are
the exact root count `2R = A(3A+b-1)+L`, the excess bound `3L ≤ E`, the
large-sector bound `3A+b ≤ 1`, the star box `-ℓ ≤ β ≤ 1`, the row floor
`Z ≥ γ + ℓ(a+b)` and the phase inequality `(A-a)Z ≤ Rβ`. -/
theorem phase_false {A b a γ ℓ R L E β Z : ℝ}
    (hA : 3 / 10 < A) (hA3 : 3 * A + b ≤ 1) (hb : 0 ≤ b)
    (ha : 0 ≤ a) (ha4 : a < 4 / 25)
    (hR : 2 * R = A * (3 * A + b - 1) + L) (hL0 : 0 ≤ L) (hL : 3 * L ≤ E)
    (hE : E < 1 / 100)
    (hγ : 27 / 500 < γ) (hl0 : 0 ≤ ℓ) (hl : ℓ < 83 / 100)
    (hβ1 : β ≤ 1) (hβ0 : -ℓ ≤ β) (hZ : γ + ℓ * (a + b) ≤ Z)
    (hphase : (A - a) * Z ≤ R * β) : False := by
  have hAa : 7 / 50 < A - a := by linarith
  have hZpos : 0 < Z := by nlinarith [mul_nonneg hl0 (add_nonneg ha hb)]
  have hlhs : 7 / 50 * (27 / 500) < (A - a) * Z := by
    have h1 : 7 / 50 * Z < (A - a) * Z := mul_lt_mul_of_pos_right hAa hZpos
    nlinarith [mul_nonneg hl0 (add_nonneg ha hb)]
  rcases lt_trichotomy R 0 with hneg | hzero | hpos
  · -- Negative phase: the star is negative and the count caps `-R`.
    have hneg' : -R ≤ A * (1 - 3 * A - b) / 2 := by linarith
    have hstar : R * β ≤ ℓ * (A * (1 - 3 * A - b) / 2) := by
      have h1 : R * β = (-R) * (-β) := by ring
      have h2 : (-R) * (-β) ≤ (-R) * ℓ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h3 : (-R) * ℓ ≤ (A * (1 - 3 * A - b) / 2) * ℓ :=
        mul_le_mul_of_nonneg_right hneg' hl0
      linarith
    have hcap : (A - a) * (γ + ℓ * (a + b)) ≤ (A - a) * Z :=
      mul_le_mul_of_nonneg_left hZ (by linarith)
    have hconcave : ℓ * (A * (1 - 3 * A - b) / 2) < (A - a) * (γ + ℓ * (a + b)) := by
      have hAup : A ≤ 1 / 3 := by linarith
      have h1 : 0 ≤ ℓ * ((A - a) * a) := mul_nonneg hl0 (by nlinarith)
      have h2 : 0 ≤ ℓ * ((A - a) * b + A * b / 2) := mul_nonneg hl0 (by nlinarith)
      have h3 : ℓ * (A * (1 - 3 * A) / 2) ≤ ℓ * (A / 20) := by
        apply mul_le_mul_of_nonneg_left _ hl0
        nlinarith
      have h4 : (A - a) * γ > 7 / 50 * γ := by nlinarith
      nlinarith
    linarith
  · rw [hzero, zero_mul] at hphase
    linarith
  · -- Positive phase: `R ≤ L/2 ≤ E/6`, too small for the row.
    have hRup : R ≤ E / 6 := by nlinarith
    have hRβ : R * β ≤ R := by nlinarith
    linarith

end Erdos1017.MiddlePrivateUnsaturatedScalar
