module

public import Erdos1017.Exclusions.E2.Lower.LowerE2ScalarCertificates
public import Mathlib.Tactic.Linarith

/-!
# Closed joined-peak certificate with the sharp coefficient

The closed joined-peak certificate holds with the sharp coefficient `ell - 2/3`
on `q ∈ [187/1000, 1/5]` and `A ∈ [3/10, 1/3]` (`joined_cost_lt`).
-/

@[expose] public section

noncomputable section

open Set

namespace Erdos1017.MiddleUnsaturatedJoinedScalar

open LowerE2Scalar

/-- The gap floor exceeds `361/6600` on the closed range `[187/1000, 1/5]`. -/
private theorem gapFloor_gt {q : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5)) :
    361 / 6600 < gapFloor q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hR := denominator_pos hq0
  have hq2 : (187 / 1000 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1 2
  unfold gapFloor
  rw [lt_div_iff₀ (by positivity)]
  unfold denominator
  norm_num at hq2
  nlinarith [hq.1]

/-- One closed peak-mass box `[al, au] ⊆ [3/10, 1/3]`. The selector value
at `ell >= 9/11` is increasing on the box, so the strict cap gives
`T < τ`; the cost is then increasing in both `t` and `T`. -/
private theorem joined_box {ell A γ T al au τ g : ℝ}
    (hell : 9 / 11 ≤ ell) (hA : A ∈ Icc al au) (hau : au ≤ 1 / 3)
    (hγ : g < γ) (hT : 0 ≤ T)
    (hcap : (ell - 2 / 3) * T ^ 2 ≤ (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 - γ)
    (hτ : 0 ≤ τ) (hτthird : τ < 1 / 3)
    (hradius : 33 / 5 * ((-1 + 8 * au - 131 / 11 * au ^ 2) / 6 - g) ≤ τ ^ 2)
    (hcost : (1 - 2 * al) ^ 2 - 9 / 22 * (1 - 2 * al - τ) ^ 2 < 1 / 8) :
    T < 1 / 3 ∧ T < 1 - 2 * A ∧
      ∀ t, 1 / 3 ≤ t → t ≤ 1 - 2 * A → t ^ 2 - ell / 2 * (t - T) ^ 2 < 1 / 8 := by
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have hell9 : (-1 + 8 * A - (7 + 6 * ell) * A ^ 2) / 6 ≤
      (-1 + 8 * A - 131 / 11 * A ^ 2) / 6 := by
    nlinarith [mul_nonneg (show 0 ≤ ell - 9 / 11 by linarith) hA2]
  have hbracket : 0 ≤ 8 - 131 / 11 * (au + A) := by linarith [hA.2]
  have hmono : (-1 + 8 * A - 131 / 11 * A ^ 2) / 6 ≤ (-1 + 8 * au - 131 / 11 * au ^ 2) / 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA.2) hbracket]
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  have hcoef : 5 / 33 * T ^ 2 ≤ (ell - 2 / 3) * T ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hT2
  have hsq : T ^ 2 < τ ^ 2 := by nlinarith
  have hTτ : T < τ := lt_of_pow_lt_pow_left₀ 2 hτ hsq
  refine ⟨by linarith, by linarith [hA.2], ?_⟩
  intro t ht htu
  have hτt : 0 ≤ t - τ := by linarith
  have h1 : (t - τ) ^ 2 ≤ (t - T) ^ 2 := pow_le_pow_left₀ hτt (by linarith) 2
  have h2 : 9 / 22 * (t - τ) ^ 2 ≤ ell / 2 * (t - T) ^ 2 :=
    mul_le_mul (by linarith) h1 (sq_nonneg _) (by linarith)
  have htop : t ≤ 1 - 2 * al := by linarith [hA.1]
  have h3 : t ^ 2 - 9 / 22 * (t - τ) ^ 2 ≤
      (1 - 2 * al) ^ 2 - 9 / 22 * (1 - 2 * al - τ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htop)
      (show 0 ≤ 13 / 22 * (1 - 2 * al + t) + 9 / 11 * τ by linarith)]
  linarith

/-- The exact closed joined-peak certificate with the sharp coefficient
`ell - 2/3`. On `q ∈ [187/1000, 1/5]` and `A ∈ [3/10, 1/3]`, every
nonnegative `T` with `(ell-2/3)T^2 <= D_ell(A) - gamma`, `gamma > g_q`,
satisfies `T < 1/3`, `T < 1-2A`, and every admissible height
`t ∈ [1/3, 1-2A]` has cost `t^2 - ell/2 (t-T)^2 < 1/8`. Two closed boxes
`[3/10, 31/100]` and `[31/100, 1/3]` with radii `9/100` and `13/100`
cover the domain; all substitutions are monotone and exact. -/
theorem joined_cost_lt {q A γ T : ℝ} (hq : q ∈ Icc (187 / 1000 : ℝ) (1 / 5))
    (hA : A ∈ Icc (3 / 10 : ℝ) (1 / 3)) (hγ : gapFloor q < γ) (hT : 0 ≤ T)
    (hcap : (multiplier q - 2 / 3) * T ^ 2 ≤
      (-1 + 8 * A - (7 + 6 * multiplier q) * A ^ 2) / 6 - γ) :
    T < 1 / 3 ∧ T < 1 - 2 * A ∧
      ∀ t, 1 / 3 ≤ t → t ≤ 1 - 2 * A → t ^ 2 - multiplier q / 2 * (t - T) ^ 2 < 1 / 8 := by
  have hden : 0 < 2 + q := by linarith [hq.1]
  have hell : 9 / 11 ≤ multiplier q := by
    unfold multiplier
    rw [le_div_iff₀ hden]
    linarith [hq.2]
  have hg := (gapFloor_gt hq).trans hγ
  by_cases hsplit : A ≤ 31 / 100
  · exact joined_box (τ := 9 / 100) hell ⟨hA.1, hsplit⟩ (by norm_num) hg hT hcap
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact joined_box (τ := 13 / 100) hell ⟨(lt_of_not_ge hsplit).le, hA.2⟩ le_rfl hg hT hcap
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Erdos1017.MiddleUnsaturatedJoinedScalar
