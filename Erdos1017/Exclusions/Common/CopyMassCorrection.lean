module

public import Erdos1017.Models.Selection.QuadraticConstraint

/-!
# Mass correction along a copy curve

This module defines `copyMassCorrectionFactor`, the exact small transverse
correction for a fresh independent mass `t²`, including its normalization term
of order `t⁴`, and shows that local maximality along the exactly corrected copy
curve forces the sign of the original-multiplier first variation
(`copy_mass_sign_of_local_max`).
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- Exact small transverse correction for a fresh independent mass t²,
including its probability-normalization term of order t⁴. -/
def copyMassCorrectionFactor (a a₂ b c d t : ℝ) : ℝ :=
  correctionFactor (a + a₂ * t ^ 2) (b + c * t ^ 2) 0 d t

theorem copyMassCorrectionFactor_continuousAt_zero (a a₂ b c d : ℝ) (hb : 0 < b) :
    ContinuousAt (copyMassCorrectionFactor a a₂ b c d) 0 := by
  unfold copyMassCorrectionFactor correctionFactor
  apply ContinuousAt.div (by fun_prop)
  · fun_prop
  · simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_sq hb.le]
    linarith

theorem copyMassCorrectionFactor_solves_eventually (a a₂ b c d : ℝ) (hb : 0 < b) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      a * t ^ 2 + a₂ * t ^ 4 +
        (b + c * t ^ 2) * (t ^ 2 * copyMassCorrectionFactor a a₂ b c d t) +
        d * (t ^ 2 * copyMassCorrectionFactor a a₂ b c d t) ^ 2 = 0 := by
  have hdisc : Continuous (fun t : ℝ =>
      (b + c * t ^ 2) ^ 2 - 4 * d * (a + a₂ * t ^ 2) * t ^ 2) := by fun_prop
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < (b + c * t ^ 2) ^ 2 - 4 * d * (a + a₂ * t ^ 2) * t ^ 2 :=
    hdisc.continuousAt.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos hb))
  have hden : Continuous (fun t : ℝ => b + c * t ^ 2 +
      Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * d * (a + a₂ * t ^ 2) * t ^ 2)) := by fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), b + c * t ^ 2 +
      Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * d * (a + a₂ * t ^ 2) * t ^ 2) ≠ 0 := by
    apply hden.continuousAt.eventually_ne
    simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_sq hb.le]
    linarith
  filter_upwards [hd, hn] with t ht hne
  have hs := Real.sq_sqrt ht.le
  have he : a * t ^ 2 + a₂ * t ^ 4 = (a + a₂ * t ^ 2) * t ^ 2 := by ring
  rw [he]
  dsimp only [copyMassCorrectionFactor, correctionFactor]
  simp only [mul_zero, zero_mul, add_zero]
  generalize hr : Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * d * (a + a₂ * t ^ 2) * t ^ 2) = r
    at hs hne ⊢
  generalize hq : b + c * t ^ 2 = q at hs hne ⊢
  generalize hv : a + a₂ * t ^ 2 = v at hs hne ⊢
  field_simp [hne]
  linear_combination v * t ^ 2 * hs

/-- Actual local maximality along the constructed exactly corrected copy
curve forces its old-multiplier first-variation sign. -/
theorem copy_mass_sign_of_local_max
    (a a₂ b c d A A₂ B C D m : ℝ) (hb : 0 < b) (hB : B = m * b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ τ s : ℝ, 0 ≤ τ → τ < ε → |s| < ε →
      a * τ + a₂ * τ ^ 2 + (b + c * τ) * s + d * s ^ 2 = 0 →
      A * τ + A₂ * τ ^ 2 + (B + C * τ) * s + D * s ^ 2 ≤ 0) : A - m * a ≤ 0 := by
  let k := copyMassCorrectionFactor a a₂ b c d
  have hk : ContinuousAt k 0 := copyMassCorrectionFactor_continuousAt_zero a a₂ b c d hb
  have hτ : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * k t) 0 := by fun_prop
  have hsmallτ : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 < ε :=
    hτ.eventually (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * k t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  let H : ℝ → ℝ := fun t => (A - m * a) + (A₂ - m * a₂) * t ^ 2 +
    (C - m * c) * t ^ 2 * k t + (D - m * d) * t ^ 2 * (k t) ^ 2
  have hH : ContinuousAt H 0 := by dsimp only [H]; fun_prop
  have hlim : Tendsto H (𝓝[>] 0) (𝓝 (A - m * a)) := by
    simpa [H] using hH.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    hsmallτ.filter_mono nhdsWithin_le_nhds, hsmalls.filter_mono nhdsWithin_le_nhds,
    (copyMassCorrectionFactor_solves_eventually a a₂ b c d hb).filter_mono nhdsWithin_le_nhds]
    with t ht hsmallτ hsmalls hroot
  have hcost := hmax (t ^ 2) (t ^ 2 * k t) (sq_nonneg t) hsmallτ hsmalls
    (by convert hroot using 1; ring)
  have hmul : t ^ 2 * H t ≤ 0 := by
    dsimp only [H]
    rw [hB] at hcost
    linear_combination hcost - m * hroot
  exact nonpos_of_mul_nonpos_right hmul (sq_pos_of_pos ht)

end Erdos1017.Variation
