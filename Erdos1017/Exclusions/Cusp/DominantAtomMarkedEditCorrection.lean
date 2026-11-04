module

public import Erdos1017.Exclusions.Common.CopyMassCorrection

/-!
# Marking correction for the dominant-atom edit

The factor `markingCorrectionFactor` keeps the mixed marking times the square of
the bounded vertex reweighting, is continuous at zero, and solves the correction
equation eventually. Local maximality of the corrected marked competitor forces
the sign of the original multiplier, with every mixed quadratic term.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- The exact marking correction retains the mixed marking times square
of the old bounded vertex reweighting. -/
def markingCorrectionFactor (a b c d e t : ℝ) : ℝ :=
  correctionFactor a (b + c * t ^ 2) 0 (d + e * t ^ 2) t

theorem markingCorrectionFactor_continuousAt_zero (a b c d e : ℝ) (hb : 0 < b) :
    ContinuousAt (markingCorrectionFactor a b c d e) 0 := by
  unfold markingCorrectionFactor correctionFactor
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_sq hb.le]
    linarith

theorem markingCorrectionFactor_solves_eventually (a b c d e : ℝ) (hb : 0 < b) :
    ∀ᶠ t in 𝓝 (0 : ℝ), a * t ^ 2 +
      (b + c * t ^ 2) * (t ^ 2 * markingCorrectionFactor a b c d e t) +
      (d + e * t ^ 2) * (t ^ 2 * markingCorrectionFactor a b c d e t) ^ 2 = 0 := by
  have hdisc : Continuous (fun t : ℝ =>
      (b + c * t ^ 2) ^ 2 - 4 * (d + e * t ^ 2) * a * t ^ 2) := by fun_prop
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < (b + c * t ^ 2) ^ 2 - 4 * (d + e * t ^ 2) * a * t ^ 2 :=
    hdisc.continuousAt.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos hb))
  have hden : Continuous (fun t : ℝ => b + c * t ^ 2 +
      Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * (d + e * t ^ 2) * a * t ^ 2)) := by fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), b + c * t ^ 2 +
      Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * (d + e * t ^ 2) * a * t ^ 2) ≠ 0 := by
    apply hden.continuousAt.eventually_ne
    simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_sq hb.le]
    linarith
  filter_upwards [hd, hn] with t ht hne
  have hs := Real.sq_sqrt ht.le
  dsimp only [markingCorrectionFactor, correctionFactor]
  simp only [mul_zero, zero_mul, add_zero]
  generalize hr : Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * (d + e * t ^ 2) * a * t ^ 2) = r at hs hne ⊢
  generalize hq : b + c * t ^ 2 = q at hs hne ⊢
  generalize hv : d + e * t ^ 2 = v at hs ⊢
  field_simp [hne]
  linear_combination a * t ^ 2 * hs

/-- Actual local maximality of the exactly corrected marked competitor
forces its original multiplier sign, with every mixed quadratic term. -/
theorem marking_sign_of_local_max
    (a b c d e A A₂ B C C₂ D E E₂ m : ℝ) (hb : 0 < b) (hB : B = m * b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ alpha s : ℝ, 0 ≤ alpha → alpha < ε → |s| < ε →
      a * alpha + (b + c * alpha) * s + (d + e * alpha) * s ^ 2 = 0 →
      A * alpha + A₂ * alpha ^ 2 + (B + C * alpha + C₂ * alpha ^ 2) * s +
        (D + E * alpha + E₂ * alpha ^ 2) * s ^ 2 ≤ 0) : A - m * a ≤ 0 := by
  let k := markingCorrectionFactor a b c d e
  have hk : ContinuousAt k 0 := markingCorrectionFactor_continuousAt_zero a b c d e hb
  have hsmallalpha : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 < ε :=
    (show ContinuousAt (fun t : ℝ => t ^ 2) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * k t| < ε :=
    (show ContinuousAt (fun t : ℝ => |t ^ 2 * k t|) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hε))
  let H : ℝ → ℝ := fun t => (A - m * a) + A₂ * t ^ 2 +
    (C - m * c) * t ^ 2 * k t + C₂ * t ^ 4 * k t +
    (D - m * d) * t ^ 2 * (k t) ^ 2 +
    (E - m * e) * t ^ 4 * (k t) ^ 2 + E₂ * t ^ 6 * (k t) ^ 2
  have hH : ContinuousAt H 0 := by dsimp only [H]; fun_prop
  have hlim : Tendsto H (𝓝[>] 0) (𝓝 (A - m * a)) := by
    simpa [H] using hH.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hsmallalpha.filter_mono nhdsWithin_le_nhds,
    hsmalls.filter_mono nhdsWithin_le_nhds,
    (markingCorrectionFactor_solves_eventually a b c d e hb).filter_mono nhdsWithin_le_nhds]
    with t ht hsmallalpha hsmalls hroot
  have hcost := hmax (t ^ 2) (t ^ 2 * k t) (sq_nonneg t) hsmallalpha hsmalls hroot
  have hmul : t ^ 2 * H t ≤ 0 := by
    dsimp only [H]
    rw [hB] at hcost
    linear_combination hcost - m * hroot
  exact nonpos_of_mul_nonpos_right hmul (sq_pos_of_pos ht)

end Erdos1017.Variation
