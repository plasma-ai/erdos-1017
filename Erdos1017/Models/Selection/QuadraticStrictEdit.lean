module

public import Erdos1017.Models.Selection.QuadraticEditCorrection

/-!
# Vanishing density derivative of a strict edit

If an affine edit preserves a shifted quadratic form with a positive transverse
direction, exact small density corrections force its density derivative to
vanish.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- If an affine edit preserves a shifted quadratic form with a positive
transverse direction, exact small density corrections force its density
derivative to vanish. -/
theorem edit_density_zero_of_positive_shift (a b c d e q : ℝ) (hb : 0 < b) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ τ s : ℝ, 0 ≤ τ → τ < ε → |s| < ε →
      a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 = 0 → q * s ^ 2 ≤ 0) : a = 0 := by
  let k := editCorrectionFactor a b c d e
  have hk : ContinuousAt k 0 := editCorrectionFactor_continuousAt_zero a b c d e hb
  have hτ : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * k t) 0 := by fun_prop
  have hsmallτ : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 < ε :=
    hτ.eventually (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * k t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ^ 2 < ε ∧ |t ^ 2 * k t| < ε ∧
      a * t ^ 2 + (b + c * t ^ 2) * (t ^ 2 * k t) +
        (d + e * t ^ 2) * (t ^ 2 * k t) ^ 2 = 0 := by
    filter_upwards [self_mem_nhdsWithin, hsmallτ.filter_mono nhdsWithin_le_nhds,
      hsmalls.filter_mono nhdsWithin_le_nhds,
      (editCorrectionFactor_solves_eventually a b c d e hb).filter_mono nhdsWithin_le_nhds]
      with t ht hτ hs hroot
    exact ⟨ht, hτ, hs, hroot⟩
  obtain ⟨t, ht, hτ, hs, hroot⟩ := hgood.exists
  have hcost := hmax (t ^ 2) (t ^ 2 * k t) (sq_nonneg t) hτ hs hroot
  have hs0 : t ^ 2 * k t = 0 := by
    have hsq : (t ^ 2 * k t) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hcost hq
    exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  rw [hs0] at hroot
  simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hroot
  exact (mul_eq_zero.mp hroot).resolve_right (sq_pos_of_pos ht).ne'

end Erdos1017.Variation
