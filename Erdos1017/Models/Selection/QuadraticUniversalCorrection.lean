module

public import Erdos1017.Models.Selection.QuadraticEditCorrection

/-!
# Transverse correction for universal mass

An exact transverse correction (`universalCorrectionFactor`) handles a
universal-mass density increment containing the normalization term
`a*(tau+tau^2/2)`, and a positive shifted direction together with the exact
universal-vertex comparison forces positive gamma.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- Exact transverse correction when the universal-mass density increment
contains the normalization term `a*(tau+tau^2/2)`. -/
def universalCorrectionFactor (a b d t : ℝ) : ℝ :=
  correctionFactor (a * (1 + t ^ 2 / 2)) b 0 d t

theorem universalCorrectionFactor_continuousAt_zero (a b d : ℝ) (hb : 0 < b) :
    ContinuousAt (universalCorrectionFactor a b d) 0 := by
  unfold universalCorrectionFactor correctionFactor
  apply ContinuousAt.div (by fun_prop)
  · fun_prop
  · simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_sq hb.le]
    linarith

theorem universalCorrectionFactor_solves_eventually (a b d : ℝ) (hb : 0 < b) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      a * (t ^ 2 + t ^ 4 / 2) + b * (t ^ 2 * universalCorrectionFactor a b d t) +
        d * (t ^ 2 * universalCorrectionFactor a b d t) ^ 2 = 0 := by
  have hdisc : Continuous (fun t : ℝ => b ^ 2 - 4 * d * (a * (1 + t ^ 2 / 2)) * t ^ 2) := by fun_prop
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < b ^ 2 - 4 * d * (a * (1 + t ^ 2 / 2)) * t ^ 2 :=
    hdisc.continuousAt.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos hb))
  have hden : Continuous (fun t : ℝ => b + Real.sqrt (b ^ 2 - 4 * d * (a * (1 + t ^ 2 / 2)) * t ^ 2)) := by fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), b + Real.sqrt (b ^ 2 - 4 * d * (a * (1 + t ^ 2 / 2)) * t ^ 2) ≠ 0 := by
    apply hden.continuousAt.eventually_ne
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero, Real.sqrt_sq hb.le]
    linarith
  filter_upwards [hd, hn] with t ht hne
  have hs := Real.sq_sqrt ht.le
  have hid : a * (t ^ 2 + t ^ 4 / 2) = (a * (1 + t ^ 2 / 2)) * t ^ 2 := by ring
  rw [hid]
  dsimp only [universalCorrectionFactor, correctionFactor]
  simp only [mul_zero, zero_mul, add_zero]
  generalize hr : Real.sqrt (b ^ 2 - 4 * d * (a * (1 + t ^ 2 / 2)) * t ^ 2) = r at hs hne ⊢
  generalize hv : a * (1 + t ^ 2 / 2) = A at hs hne ⊢
  field_simp [hne]
  linear_combination A * t ^ 2 * hs

/-- A positive shifted direction and the exact universal-vertex comparison
force positive gamma; no first-order or asymptotic inequality is assumed. -/
theorem gamma_pos_of_universal_comparison (a b d q γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ τ s : ℝ, 0 ≤ τ → τ < ε → |s| < ε →
      a * (τ + τ ^ 2 / 2) + b * s + d * s ^ 2 = 0 →
      q * s ^ 2 ≤ 2 * γ * (τ + τ ^ 2 / 2)) : 0 < γ := by
  let k := universalCorrectionFactor a b d
  have hk : ContinuousAt k 0 := universalCorrectionFactor_continuousAt_zero a b d hb
  have hτ : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * k t) 0 := by fun_prop
  have hsmallτ : ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 < ε :=
    hτ.eventually (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * k t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ^ 2 < ε ∧ |t ^ 2 * k t| < ε ∧
      a * (t ^ 2 + t ^ 4 / 2) + b * (t ^ 2 * k t) + d * (t ^ 2 * k t) ^ 2 = 0 := by
    filter_upwards [self_mem_nhdsWithin, hsmallτ.filter_mono nhdsWithin_le_nhds,
      hsmalls.filter_mono nhdsWithin_le_nhds,
      (universalCorrectionFactor_solves_eventually a b d hb).filter_mono nhdsWithin_le_nhds]
      with t ht hτ hs hroot
    exact ⟨ht, hτ, hs, hroot⟩
  obtain ⟨t, ht, hτ, hs, hroot⟩ := hgood.exists
  have hstep : 0 < t ^ 2 + t ^ 4 / 2 := by positivity
  have hsne : t ^ 2 * k t ≠ 0 := by
    intro hzero
    rw [hzero] at hroot
    simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hroot
    exact (mul_pos ha hstep).ne' hroot
  have hcost := hmax (t ^ 2) (t ^ 2 * k t) (sq_nonneg t) hτ hs (by convert hroot using 1; ring)
  have hpos : 0 < q * (t ^ 2 * k t) ^ 2 := mul_pos hq (sq_pos_of_ne_zero hsne)
  by_contra hγ
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2)
    (not_lt.mp hγ)) (by positivity : 0 ≤ t ^ 2 + (t ^ 2) ^ 2 / 2)
  linarith

end Erdos1017.Variation
