module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Exact corrections on a quadratic constraint

A bounded factor `correctionFactor` gives the exact small-branch solution of a
quadratic constraint near zero, and local maximality on a regular quadratic
constraint determines the tangent first variation and the multiplier-adjusted
second variation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Erdos1017.Variation

/-- The bounded factor in the small branch of an exact quadratic constraint
correction. The actual correction is `t² * correctionFactor a b c d t`. -/
def correctionFactor (a b c d t : ℝ) : ℝ :=
  -2 * a / (b + 2 * c * t + Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * a * t ^ 2))

theorem correctionFactor_zero (a b c d : ℝ) (hb : 0 < b) :
    correctionFactor a b c d 0 = -a / b := by
  simp only [correctionFactor, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    Real.sqrt_sq hb.le]
  field_simp
  ring

theorem correctionFactor_continuousAt_zero (a b c d : ℝ) (hb : 0 < b) :
    ContinuousAt (correctionFactor a b c d) 0 := by
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_sq hb.le]
    linarith

/-- The small branch solves the constraint exactly near zero, including
when the coefficient of the correction's square vanishes. -/
theorem correctionFactor_solves_eventually (a b c d : ℝ) (hb : 0 < b) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      a * t ^ 2 + (b + 2 * c * t) * (t ^ 2 * correctionFactor a b c d t) +
        d * (t ^ 2 * correctionFactor a b c d t) ^ 2 = 0 := by
  have hdisc : Continuous (fun t : ℝ => (b + 2 * c * t) ^ 2 - 4 * d * a * t ^ 2) := by fun_prop
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (b + 2 * c * t) ^ 2 - 4 * d * a * t ^ 2 := by
    exact hdisc.continuousAt.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos hb))
  have hden : Continuous (fun t : ℝ => b + 2 * c * t +
      Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * a * t ^ 2)) := by fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), b + 2 * c * t +
      Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * a * t ^ 2) ≠ 0 := by
    apply hden.continuousAt.eventually_ne
    simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_sq hb.le]
    linarith
  filter_upwards [hd, hn] with t ht hne
  have hs := Real.sq_sqrt ht.le
  dsimp [correctionFactor]
  generalize hr : Real.sqrt ((b + 2 * c * t) ^ 2 - 4 * d * a * t ^ 2) = r at hs hne ⊢
  generalize hq : b + 2 * c * t = q at hs hne ⊢
  field_simp [hne]
  linear_combination a * t ^ 2 * hs

/-- Exact local maximality on a quadratic constraint forces nonpositivity
of its tangent quadratic coefficient. A nonzero transverse derivative is
encoded by `b > 0`; no implicit-function or correction hypothesis is assumed. -/
theorem tangent_quadratic_nonpos_of_local_max
    (a b c d A C D : ℝ) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ t s : ℝ, |t| < ε → |s| < ε →
      a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2 = 0 →
      A * t ^ 2 + 2 * C * t * s + D * s ^ 2 ≤ 0) : A ≤ 0 := by
  let q := correctionFactor a b c d
  have hq : ContinuousAt q 0 := correctionFactor_continuousAt_zero a b c d hb
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * q t) 0 := by fun_prop
  have hsmallt : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ε :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * q t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hcost : ContinuousAt (fun t : ℝ => A + 2 * C * t * q t + D * t ^ 2 * (q t) ^ 2) 0 := by
    fun_prop
  have hlim : Tendsto (fun t : ℝ => A + 2 * C * t * q t + D * t ^ 2 * (q t) ^ 2)
      (𝓝[>] 0) (𝓝 A) := by
    simpa using hcost.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  apply le_of_tendsto hlim
  filter_upwards [hpos, hsmallt.filter_mono nhdsWithin_le_nhds,
    hsmalls.filter_mono nhdsWithin_le_nhds,
    (correctionFactor_solves_eventually a b c d hb).filter_mono nhdsWithin_le_nhds]
    with t ht hsmallt hsmalls hroot
  have h := hmax t (t ^ 2 * q t) hsmallt hsmalls hroot
  have hm : t ^ 2 * (A + 2 * C * t * q t + D * t ^ 2 * (q t) ^ 2) ≤ 0 := by
    convert h using 1
    ring
  exact nonpos_of_mul_nonpos_right hm (sq_pos_of_pos ht)

theorem tangent_linear_nonpos_of_local_max
    (a b c d L M A C D : ℝ) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ t s : ℝ, |t| < ε → |s| < ε →
      a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2 = 0 →
      L * t + M * s + A * t ^ 2 + 2 * C * t * s + D * s ^ 2 ≤ 0) : L ≤ 0 := by
  let q := correctionFactor a b c d
  have hq : ContinuousAt q 0 := correctionFactor_continuousAt_zero a b c d hb
  have hs : ContinuousAt (fun t : ℝ => t ^ 2 * q t) 0 := by fun_prop
  have hsmallt : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ε :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hsmalls : ∀ᶠ t in 𝓝 (0 : ℝ), |t ^ 2 * q t| < ε :=
    hs.abs.eventually (gt_mem_nhds (by simpa using hε))
  have hcost : ContinuousAt
      (fun t : ℝ => L + M * t * q t + A * t + 2 * C * t ^ 2 * q t + D * t ^ 3 * (q t) ^ 2) 0 := by
    fun_prop
  have hlim : Tendsto
      (fun t : ℝ => L + M * t * q t + A * t + 2 * C * t ^ 2 * q t + D * t ^ 3 * (q t) ^ 2)
      (𝓝[>] 0) (𝓝 L) := by
    simpa using hcost.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  apply le_of_tendsto hlim
  filter_upwards [hpos, hsmallt.filter_mono nhdsWithin_le_nhds,
    hsmalls.filter_mono nhdsWithin_le_nhds,
    (correctionFactor_solves_eventually a b c d hb).filter_mono nhdsWithin_le_nhds]
    with t ht hsmallt hsmalls hroot
  have h := hmax t (t ^ 2 * q t) hsmallt hsmalls hroot
  have hm : t * (L + M * t * q t + A * t + 2 * C * t ^ 2 * q t + D * t ^ 3 * (q t) ^ 2) ≤ 0 := by
    convert h using 1
    ring
  exact nonpos_of_mul_nonpos_right hm ht

/-- A regular quadratic constraint and actual local maximality determine the
tangent first variation and the multiplier-adjusted second variation. -/
theorem lagrange_tangent_conditions_of_local_max
    (a b c d L M A C D : ℝ) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε)
    (hmax : ∀ t s : ℝ, |t| < ε → |s| < ε →
      a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2 = 0 →
      L * t + M * s + A * t ^ 2 + 2 * C * t * s + D * s ^ 2 ≤ 0) :
    L = 0 ∧ A - M * a / b ≤ 0 := by
  have hL := tangent_linear_nonpos_of_local_max a b c d L M A C D hb ε hε hmax
  have hneg := tangent_linear_nonpos_of_local_max a b (-c) d (-L) M A (-C) D hb ε hε (by
    intro t s ht hs hroot
    have hr : a * (-t) ^ 2 + (b + 2 * c * (-t)) * s + d * s ^ 2 = 0 := by
      convert hroot using 1
      ring
    have h := hmax (-t) s (by simpa using ht) hs hr
    convert h using 1
    ring)
  have hzero : L = 0 := by linarith
  refine ⟨hzero, ?_⟩
  apply tangent_quadratic_nonpos_of_local_max a b c d (A - M * a / b)
    (C - M * c / b) (D - M * d / b) hb ε hε
  intro t s ht hs hroot
  have h := hmax t s ht hs hroot
  rw [hzero] at h
  have heq : (A - M * a / b) * t ^ 2 + 2 * (C - M * c / b) * t * s +
      (D - M * d / b) * s ^ 2 =
      M * s + A * t ^ 2 + 2 * C * t * s + D * s ^ 2 -
        (M / b) * (a * t ^ 2 + (b + 2 * c * t) * s + d * s ^ 2) := by
    field_simp
    ring
  rw [heq, hroot, mul_zero, sub_zero]
  simpa using h

end Erdos1017.Variation
