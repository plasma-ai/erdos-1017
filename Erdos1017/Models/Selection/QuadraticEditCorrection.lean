module

public import Erdos1017.Models.Selection.QuadraticConstraint

/-!
# Density correction for small edits

An exact small quadratic correction (`editCorrectionFactor`) handles an edit of
size `t²` whose weighted density coefficients depend linearly on the edit, and
one-sided edit maximality forces the edit derivative to satisfy the same
multiplier as the transverse vertex direction.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- Exact small quadratic correction for an edit of size `t²` whose
weighted density coefficients also depend linearly on that edit. -/
def editCorrectionFactor (a b c d e t : ℝ) : ℝ :=
  correctionFactor a (b + c * t ^ 2) 0 (d + e * t ^ 2) t

theorem editCorrectionFactor_continuousAt_zero (a b c d e : ℝ) (hb : 0 < b) :
    ContinuousAt (editCorrectionFactor a b c d e) 0 := by
  unfold editCorrectionFactor correctionFactor
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_sq hb.le]
    linarith

theorem editCorrectionFactor_solves_eventually (a b c d e : ℝ) (hb : 0 < b) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      a * t ^ 2 + (b + c * t ^ 2) * (t ^ 2 * editCorrectionFactor a b c d e t) +
        (d + e * t ^ 2) * (t ^ 2 * editCorrectionFactor a b c d e t) ^ 2 = 0 := by
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
  dsimp only [editCorrectionFactor, correctionFactor]
  simp only [mul_zero, zero_mul, add_zero]
  generalize hr : Real.sqrt ((b + c * t ^ 2) ^ 2 - 4 * (d + e * t ^ 2) * a * t ^ 2) = r at hs hne ⊢
  generalize hq : b + c * t ^ 2 = q at hs hne ⊢
  generalize hv : d + e * t ^ 2 = v at hs hne ⊢
  field_simp [hne]
  linear_combination a * t ^ 2 * hs

/-- Actual one-sided edit maximality forces the edit derivative to satisfy
the same multiplier as the transverse vertex direction. All density
corrections are constructed explicitly, including the mixed edit terms. -/
theorem edit_sign_of_local_max
    (a b c d e A B C D E m : ℝ) (hb : 0 < b) (hB : B = m * b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ τ s : ℝ, 0 ≤ τ → τ < ε → |s| < ε →
      a * τ + (b + c * τ) * s + (d + e * τ) * s ^ 2 = 0 →
      A * τ + (B + C * τ) * s + (D + E * τ) * s ^ 2 ≤ 0) : A - m * a ≤ 0 := by
  let q := editCorrectionFactor a b c d e
  have hq : ContinuousAt q 0 := editCorrectionFactor_continuousAt_zero a b c d e hb
  have hτ : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * q t) 0 := by fun_prop
  have hsmallτ : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 < ε :=
    hτ.eventually (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * q t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  let H : ℝ → ℝ := fun t => (A - m * a) + (C - m * c) * t ^ 2 * q t +
    (D - m * d) * t ^ 2 * (q t) ^ 2 + (E - m * e) * t ^ 4 * (q t) ^ 2
  have hH : ContinuousAt H 0 := by dsimp only [H]; fun_prop
  have hlim : Tendsto H (𝓝[>] 0) (𝓝 (A - m * a)) := by
    simpa [H] using hH.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    hsmallτ.filter_mono nhdsWithin_le_nhds, hsmalls.filter_mono nhdsWithin_le_nhds,
    (editCorrectionFactor_solves_eventually a b c d e hb).filter_mono nhdsWithin_le_nhds]
    with t ht hsmallτ hsmalls hroot
  have hcost := hmax (t ^ 2) (t ^ 2 * q t) (sq_nonneg t) hsmallτ hsmalls hroot
  have hmul : t ^ 2 * H t ≤ 0 := by
    dsimp only [H]
    rw [hB] at hcost
    linear_combination hcost - m * hroot
  exact nonpos_of_mul_nonpos_right hmul (sq_pos_of_pos ht)

end Erdos1017.Variation
