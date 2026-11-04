module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Correlated source loss bound

The signed source coefficients are paid once by the maximum
`L = max LI (max LJ LD)` of the one-sided and cross coefficients, the cross
coefficient never exceeding the larger one-sided one (`source_loss_le`,
`source_loss_le_sqrt`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CorrelatedSourceLoss

/-- The cross coefficient never exceeds the larger one-sided coefficient: it vanishes unless
`1/2 - X` and `1/2 - t` have opposite signs, and then it is `LI` or `LJ` times a factor in
`[0, 1]`. -/
theorem cross_le_max {X t LI LJ LC : ℝ} (hX : 0 < X) (ht : 0 < t)
    (hLI : LI = max (1 / 2 - X) 0 / X) (hLJ : LJ = max (1 / 2 - t) 0 / t)
    (hLC : LC = max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t)) :
    LC ≤ max LI LJ := by
  have hLI0 : 0 ≤ LI := by
    rw [hLI]
    exact div_nonneg (le_max_right _ _) hX.le
  rcases le_or_gt (-(1 / 2 - X) * (1 / 2 - t)) 0 with hC | hC
  · rw [hLC, max_eq_right hC, zero_div]
    exact le_trans hLI0 (le_max_left _ _)
  rw [hLC, max_eq_left hC.le]
  rcases le_total (1 / 2 - X) 0 with hXf | hXn
  · have htn : 0 < 1 / 2 - t := by nlinarith
    refine le_trans ?_ (le_max_right _ _)
    rw [hLJ, max_eq_left htn.le, div_le_div_iff₀ (by positivity) ht]
    nlinarith [mul_nonneg htn.le ht.le]
  · have htf : 1 / 2 - t < 0 := by nlinarith
    refine le_trans ?_ (le_max_left _ _)
    rw [hLI, max_eq_left hXn, div_le_div_iff₀ (by positivity) hX]
    nlinarith [mul_nonneg hXn hX.le]

/-- The selected loss coefficient is nonnegative. -/
theorem coefficient_nonneg {X LI LJ LD L : ℝ} (hX : 0 < X)
    (hLI : LI = max (1 / 2 - X) 0 / X) (hL : L = max LI (max LJ LD)) :
    0 ≤ L := by
  rw [hL, hLI]
  exact le_trans (div_nonneg (le_max_right _ _) hX.le) (le_max_left _ _)

/-- Correlated source loss: the signed source coefficients are paid once by
`L = max LI (max LJ LD)` against `X cI + CJ + X Phi + FJ / 2`. The remainder energy is
paid either coefficientwise, when `(1 - t) / t ≤ L`, or through the trace
`FJ / 2 ≤ ((t + r) / 2) Phi`, when the pair `(Phi, FJ)` is priced by `LD`. -/
theorem source_loss_le {X t r cI CJ Phi FJ LI LJ LC LD L : ℝ}
    (hX : 0 < X) (ht : 0 < t) (hr : 0 < r) (hr2 : r ^ 2 = t ^ 2 + 2 * X * t)
    (hLI : LI = max (1 / 2 - X) 0 / X) (hLJ : LJ = max (1 / 2 - t) 0 / t)
    (hLC : LC = max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t))
    (hLD : LD = (LC * (r - t) + 1 - t) / r) (hL : L = max LI (max LJ LD))
    (hcI : 0 ≤ cI) (hCJ : 0 ≤ CJ) (hPhi : 0 ≤ Phi) (hFJ : 0 ≤ FJ)
    (htrace : FJ / 2 ≤ ((t + r) / 2) * Phi) :
    (1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
        ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t) ≤
      L * (X * cI + CJ + X * Phi + FJ / 2) := by
  have hLIL : LI ≤ L := by
    rw [hL]
    exact le_max_left _ _
  have hLJL : LJ ≤ L := by
    rw [hL]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hLDL : LD ≤ L := by
    rw [hL]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hLCL : LC ≤ L :=
    le_trans (cross_le_max hX ht hLI hLJ hLC) (max_le hLIL hLJL)
  -- Peak credit.
  have hI : (1 / 2 - X) * cI ≤ L * (X * cI) := by
    have hLIX : LI * X = max (1 / 2 - X) 0 := by
      rw [hLI]
      field_simp
    have hcoef : 1 / 2 - X ≤ L * X := by
      nlinarith [le_max_left (1 / 2 - X) 0, mul_le_mul_of_nonneg_right hLIL hX.le]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hcI]
  -- Remainder credit.
  have hJ : ((1 / 2 - t) / t) * CJ ≤ L * CJ := by
    have hcoef : (1 / 2 - t) / t ≤ L := by
      refine le_trans ?_ hLJL
      rw [hLJ]
      exact div_le_div_of_nonneg_right (le_max_left _ _) ht.le
    exact mul_le_mul_of_nonneg_right hcoef hCJ
  -- Cross energy, paid by `LC`.
  have hCX : -((1 / 2 - X) * (1 / 2 - t) / t) ≤ LC * X := by
    have hLCX : LC * X = max (-(1 / 2 - X) * (1 / 2 - t)) 0 / t := by
      rw [hLC]
      field_simp
    rw [hLCX, ← neg_div, neg_mul]
    exact div_le_div_of_nonneg_right (le_max_left _ _) ht.le
  -- Correlated pair `(Phi, FJ)`.
  have hpair : LC * X * Phi + ((1 - t) / t) * (FJ / 2) ≤ L * (X * Phi + FJ / 2) := by
    rcases le_or_gt ((1 - t) / t) L with hT | hT
    · nlinarith [mul_le_mul_of_nonneg_right hLCL (mul_nonneg hX.le hPhi),
        mul_le_mul_of_nonneg_right hT (by linarith : (0 : ℝ) ≤ FJ / 2)]
    · have hLDr : LD * r = LC * (r - t) + 1 - t := by
        rw [hLD]
        field_simp
      have hLTt : (1 - t) / t * t = 1 - t := div_mul_cancel₀ _ ht.ne'
      have hid : LD * (X + (t + r) / 2) = LC * X + ((1 - t) / t) * ((t + r) / 2) := by
        refine mul_right_cancel₀ (mul_ne_zero hr.ne' ht.ne') ?_
        linear_combination ((X + (t + r) / 2) * t) * hLDr - ((t + r) / 2 * r) * hLTt +
          (LC * t / 2 - (1 - t) / 2) * hr2
      have hh : 0 ≤ X + (t + r) / 2 := by positivity
      have hw := mul_le_mul_of_nonneg_left htrace (sub_pos.mpr hT).le
      have hD := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLDL hh) hPhi
      nlinarith
  have hsplit : (1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
        ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t) =
      (1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ +
        -((1 / 2 - X) * (1 / 2 - t) / t) * Phi + ((1 - t) / t) * (FJ / 2) := by
    ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hCX hPhi]

/-- The same loss with the literal radical `r = √(t^2 + 2Xt)`. -/
theorem source_loss_le_sqrt {X t cI CJ Phi FJ : ℝ} (hX : 0 < X) (ht : 0 < t)
    (hcI : 0 ≤ cI) (hCJ : 0 ≤ CJ) (hPhi : 0 ≤ Phi) (hFJ : 0 ≤ FJ)
    (htrace : FJ / 2 ≤ ((t + Real.sqrt (t ^ 2 + 2 * X * t)) / 2) * Phi) :
    (1 / 2 - X) * cI + ((1 / 2 - t) / t) * CJ -
        ((1 / 2 - X) * (1 / 2 - t) / t) * Phi + (1 - t) * FJ / (2 * t) ≤
      max (max (1 / 2 - X) 0 / X) (max (max (1 / 2 - t) 0 / t)
          ((max (-(1 / 2 - X) * (1 / 2 - t)) 0 / (X * t) *
              (Real.sqrt (t ^ 2 + 2 * X * t) - t) + 1 - t) /
            Real.sqrt (t ^ 2 + 2 * X * t))) *
        (X * cI + CJ + X * Phi + FJ / 2) := by
  have hpos : 0 < t ^ 2 + 2 * X * t := by positivity
  exact source_loss_le (r := Real.sqrt (t ^ 2 + 2 * X * t)) hX ht
    (Real.sqrt_pos.2 hpos) (Real.sq_sqrt hpos.le) rfl rfl rfl rfl rfl
    hcI hCJ hPhi hFJ htrace

end Erdos1017.CorrelatedSourceLoss
