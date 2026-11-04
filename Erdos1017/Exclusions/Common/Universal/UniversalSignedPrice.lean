module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith

/-!
# Signed copy price at an outside vertex

This module defines the signed copy price at a fixed outside vertex with the
same hole and atom-mass profiles, integrates the copied-row estimate keeping the
own-atom and outside-own allowances as separate moments, and shows that one
weighted hole inventory forces a strictly positive price and rules out a
nonpositive one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.UniversalSignedPrice

/-- The signed original copy price at a fixed outside vertex. The same
actual hole and atom-mass profiles are used at every charge value. -/
def priceFunction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (H : Set Ω) (a D : Ω → ℝ)
    (A b γ θ ax j v : ℝ) : ℝ :=
  ∫ h in H, max (b * v - γ + (D h - θ) * j) 0 /
    (A - a h - ax) ∂μ

/-- A positive constant fiber contributes its mass squared to a
nonnegative hole inventory. -/
theorem atom_square_le_total {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H I : Set Ω) (a : Ω → ℝ)
    (hfi : IntegrableOn a H μ)
    (ha : 0 ≤ᵐ[μ.restrict H] a)
    (hIH : I ≤ᵐ[μ] H)
    (hconst : a =ᵐ[μ.restrict I] fun _ => μ.real I) :
    (μ.real I) ^ 2 ≤ ∫ x in H, a x ∂μ := by
  have hle := setIntegral_mono_set hfi ha hIH
  have hI : (∫ x in I, a x ∂μ) = μ.real I * μ.real I := by
    rw [integral_congr_ae hconst, setIntegral_const, smul_eq_mul]
  rw [hI] at hle
  simpa only [pow_two] using hle

/-- A strictly positive integrable price on a positive measurable
region has strictly positive integral. -/
theorem setIntegral_pos_of_ae_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (B : Set Ω) (hB : MeasurableSet B)
    (hBpos : 0 < μ B) (f : Ω → ℝ)
    (hfi : IntegrableOn f B μ)
    (hf : ∀ᵐ x ∂μ.restrict B, 0 < f x) :
    0 < ∫ x in B, f x ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (hf.mono (fun _ h => h.le)) hfi]
  have hsupport : Function.support f ∩ B =ᵐ[μ] B := by
    have hbase := (ae_restrict_iff' hB).mp hf
    filter_upwards [hbase] with x hx
    exact propext ⟨fun h => h.2, fun h => ⟨by
      change f x ≠ 0
      exact ne_of_gt (hx h), h⟩⟩
  rw [measure_congr hsupport]
  exact hBpos

/-- The zero-price margin makes the entire copy numerator vanish at
zero charge, including when `1 - 2θ` is nonpositive. -/
theorem zero_price_numerator (γ θ R D j : ℝ)
    (hD : D ≤ 1 - θ) (hj : 0 ≤ j) (hjR : j ≤ R)
    (hmargin : max (1 - 2 * θ) 0 * R < γ) :
    max (-γ + (D - θ) * j) 0 = 0 := by
  have hcoef : D - θ ≤ max (1 - 2 * θ) 0 := by
    exact (by linarith : D - θ ≤ 1 - 2 * θ).trans (le_max_left _ _)
  have hmax : 0 ≤ max (1 - 2 * θ) 0 := le_max_right _ _
  have hprod : (D - θ) * j ≤ max (1 - 2 * θ) 0 * R := by
    nlinarith [mul_nonneg hmax (sub_nonneg.mpr hjR),
      mul_nonneg (sub_nonneg.mpr hcoef) hj]
  rw [max_eq_right (by linarith : -γ + (D - θ) * j ≤ 0)]

theorem priceFunction_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Set Ω) (a D : Ω → ℝ)
    (A b γ θ ax j R : ℝ)
    (hD : ∀ᵐ h ∂μ.restrict H, D h ≤ 1 - θ)
    (hj : 0 ≤ j) (hjR : j ≤ R)
    (hmargin : max (1 - 2 * θ) 0 * R < γ) :
    priceFunction μ H a D A b γ θ ax j 0 = 0 := by
  unfold priceFunction
  have heq : (fun h => max (b * 0 - γ + (D h - θ) * j) 0 /
      (A - a h - ax)) =ᵐ[μ.restrict H] (fun _ => (0 : ℝ)) := by
    filter_upwards [hD] with h hh
    simp only [mul_zero, zero_sub]
    rw [zero_price_numerator γ θ R (D h) j hh hj hjR hmargin]
    simp
  rw [integral_congr_ae heq]
  simp

/-- A copied charge is bounded by its signed positive-part price plus
the separately paid nonnegative missing-recipient error. -/
theorem copied_charge_le_price_integrand
    (A ah ax v numerator error : ℝ)
    (hden : 0 < A - ah - ax) (herror : 0 ≤ error)
    (hcopy : 0 < v → (A - ah - ax) * v ≤ numerator + error) :
    v ≤ max numerator 0 / (A - ah - ax) + error / (A - ah - ax) := by
  by_cases hv : 0 < v
  · have hnum := le_max_left numerator 0
    have hbound := hcopy hv
    calc
      v ≤ (max numerator 0 + error) / (A - ah - ax) :=
        (le_div_iff₀ hden).mpr (by nlinarith only [hbound, hnum])
      _ = _ := add_div _ _ _
  · have hpos : 0 ≤ max numerator 0 / (A - ah - ax) +
        error / (A - ah - ax) :=
      add_nonneg (div_nonneg (le_max_right _ _) hden.le)
        (div_nonneg herror hden.le)
    exact (le_of_not_gt hv).trans hpos

/-- A single atom's positive deficit is paid by its share of the same
total deficit. The zero-mass case includes genuine diffuse dust. -/
theorem positive_deficit_ratio_le (θ k DH a D : ℝ)
    (hθ : 0 ≤ θ) (hθhalf : θ < 1 / 2)
    (hk : 0 < k) (hDH : 0 ≤ DH) (hDHk : DH < θ * k)
    (hak : a < k)
    (hD : 0 ≤ D) (hDmax : D ≤ 1 - θ)
    (hbudget : a * D ≤ DH) :
    max (D - θ) 0 / (k - a) ≤
      D * (1 - 2 * θ) / (k * (1 - θ) - DH) := by
  have hka : 0 < k - a := by linarith
  have hθpos : 0 < θ := by
    by_contra hn
    have : θ = 0 := le_antisymm (le_of_not_gt hn) hθ
    subst θ
    nlinarith
  have hden : 0 < k * (1 - θ) - DH := by
    have htwo : 0 < 1 - 2 * θ := by linarith
    nlinarith [mul_pos hk htwo]
  by_cases hDθ : D ≤ θ
  · rw [max_eq_right (sub_nonpos.mpr hDθ), zero_div]
    exact div_nonneg (mul_nonneg hD (by linarith)) hden.le
  · have hDθpos : 0 < D - θ := sub_pos.mpr (lt_of_not_ge hDθ)
    rw [max_eq_left hDθpos.le]
    apply (div_le_div_iff₀ hka hden).2
    have hfirst : 0 ≤ (1 - θ - D) * (k * θ - a * D) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hsecond : 0 ≤ (D - θ) * (DH - a * D) :=
      mul_nonneg hDθpos.le (by linarith)
    have hid :
        D * (1 - 2 * θ) * (k - a) -
          (D - θ) * (k * (1 - θ) - DH) =
        (1 - θ - D) * (k * θ - a * D) +
          (D - θ) * (DH - a * D) := by ring
    linarith

/-- A reciprocal denominator uses the same atom-square inventory as the
hole budget. This bound remains valid at zero atom mass. -/
theorem reciprocal_denominator_le (A z α a ax : ℝ)
    (hk : 0 < A - z) (hα : α < A - z)
    (ha : 0 ≤ a) (haα : a ≤ α) (hax : ax ≤ z) :
    1 / (A - a - ax) ≤
      1 / (A - z) + a / ((A - z) * (A - z - α)) := by
  let k := A - z
  have hk' : 0 < k := hk
  have hα' : α < k := hα
  have hka : 0 < k - a := by dsimp [k] at *; linarith
  have hden : 0 < A - a - ax := by dsimp [k] at *; linarith
  have hfirst : 1 / (A - a - ax) ≤ 1 / (k - a) := by
    apply (div_le_div_iff₀ hden hka).2
    nlinarith
  have hsecond : 1 / (k - a) ≤ 1 / k + a / (k * (k - α)) := by
    have hαden : 0 < k - α := by linarith
    have hprod : 0 < k * (k - α) := mul_pos hk' hαden
    have hratio : a / (k * (k - a)) ≤ a / (k * (k - α)) := by
      apply (div_le_div_iff₀ (mul_pos hk' hka) hprod).2
      nlinarith [mul_nonneg ha (sub_nonneg.mpr haα)]
    have hid : 1 / (k - a) = 1 / k + a / (k * (k - a)) := by
      field_simp
      ring
    rw [hid]
    simpa only [add_comm] using add_le_add_left hratio (1 / k)
  exact hfirst.trans (by simpa only [k] using hsecond)

/-- Integrate the reciprocal bound once against the original atom-mass
function. No atom can spend a second square-mass allowance. -/
theorem reciprocal_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Set Ω) (a : Ω → ℝ) (A z α ax q : ℝ)
    (hk : 0 < A - z) (hα : α < A - z) (hax : ax ≤ z)
    (ha : IntegrableOn a H μ)
    (hrec : IntegrableOn (fun x => 1 / (A - a x - ax)) H μ)
    (haBounds : ∀ᵐ x ∂μ.restrict H, 0 ≤ a x ∧ a x ≤ α)
    (hquare : (∫ x in H, a x ∂μ) ≤ q) :
    (∫ x in H, 1 / (A - a x - ax) ∂μ) ≤
      μ.real H / (A - z) + q / ((A - z) * (A - z - α)) := by
  have hden : 0 < (A - z) * (A - z - α) :=
    mul_pos hk (sub_pos.mpr hα)
  have hupper : (∫ x in H, 1 / (A - a x - ax) ∂μ) ≤
      ∫ x in H, 1 / (A - z) + a x / ((A - z) * (A - z - α)) ∂μ := by
    apply integral_mono_ae hrec
      ((integrable_const (1 / (A - z))).add (ha.div_const _))
    filter_upwards [haBounds] with x hx
    exact reciprocal_denominator_le A z α (a x) ax hk hα hx.1 hx.2 hax
  have hdiv : (∫ x in H, a x / ((A - z) * (A - z - α)) ∂μ) =
      (∫ x in H, a x ∂μ) / ((A - z) * (A - z - α)) :=
    integral_div _ _
  rw [integral_add (integrable_const (1 / (A - z))) (ha.div_const _),
    hdiv, setIntegral_const, smul_eq_mul] at hupper
  have hq : (∫ x in H, a x ∂μ) / ((A - z) * (A - z - α)) ≤
      q / ((A - z) * (A - z - α)) :=
    div_le_div_of_nonneg_right hquare hden.le
  calc
    _ ≤ μ.real H * (1 / (A - z)) +
        (∫ x in H, a x ∂μ) / ((A - z) * (A - z - α)) := hupper
    _ ≤ _ := by
      simpa only [div_eq_mul_inv, one_mul, add_comm] using
        add_le_add_left hq (μ.real H * (A - z)⁻¹)

/-- The whole hole deficit pays its positive part once. An atom contributes
its own mass times its constant deficit; dust has zero own mass. -/
theorem positive_deficit_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Set Ω) (a D : Ω → ℝ) (θ k DH : ℝ)
    (hθ : 0 ≤ θ) (hθhalf : θ < 1 / 2)
    (hk : 0 < k) (hDH : 0 ≤ DH) (hDHk : DH < θ * k)
    (hDint : IntegrableOn D H μ)
    (hratio : IntegrableOn (fun x => max (D x - θ) 0 / (k - a x)) H μ)
    (hDsum : (∫ x in H, D x ∂μ) = DH)
    (hpoint : ∀ᵐ x ∂μ.restrict H,
      a x < k ∧ 0 ≤ D x ∧ D x ≤ 1 - θ ∧ a x * D x ≤ DH) :
    (∫ x in H, max (D x - θ) 0 / (k - a x) ∂μ) ≤
      DH * (1 - 2 * θ) / (k * (1 - θ) - DH) := by
  let c := (1 - 2 * θ) / (k * (1 - θ) - DH)
  have hpt : ∀ᵐ x ∂μ.restrict H,
      max (D x - θ) 0 / (k - a x) ≤ D x * c := by
    filter_upwards [hpoint] with x hx
    simpa only [c, div_eq_mul_inv, mul_assoc] using
      positive_deficit_ratio_le θ k DH (a x) (D x)
        hθ hθhalf hk hDH hDHk hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hbound := integral_mono_ae hratio (hDint.mul_const c) hpt
  rw [integral_mul_const, hDsum] at hbound
  simpa only [c, div_eq_mul_inv, mul_assoc] using hbound

/-- At or above the half threshold the hole deficit contributes no
positive numerator, independently of the hole atom masses. -/
theorem nonpositive_deficit_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Set Ω) (a D : Ω → ℝ) (θ k : ℝ)
    (hθ : 1 / 2 ≤ θ)
    (hD : ∀ᵐ x ∂μ.restrict H, D x ≤ 1 - θ) :
    (∫ x in H, max (D x - θ) 0 / (k - a x) ∂μ) = 0 := by
  have hzero : ∀ᵐ x ∂μ.restrict H,
      max (D x - θ) 0 / (k - a x) = 0 := by
    filter_upwards [hD] with x hx
    rw [max_eq_right (by linarith : D x - θ ≤ 0), zero_div]
  rw [integral_congr_ae hzero]
  simp

/-- The positive part lies below the chord from a nonpositive base to
the priced endpoint. The endpoint may itself be nonpositive. -/
theorem positive_part_chord (base endpoint t : ℝ)
    (hbase : base ≤ 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max ((1 - t) * base + t * endpoint) 0 ≤ t * max endpoint 0 := by
  have h1t : 0 ≤ 1 - t := by linarith
  by_cases hend : endpoint ≤ 0
  · rw [max_eq_right hend]
    have hbaseprod := mul_nonpos_of_nonneg_of_nonpos h1t hbase
    have hendprod := mul_nonpos_of_nonneg_of_nonpos ht0 hend
    rw [max_eq_right (by linarith : (1 - t) * base + t * endpoint ≤ 0)]
    simp
  · rw [max_eq_left (le_of_not_ge hend)]
    apply max_le
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos h1t hbase]
    · exact mul_nonneg ht0 (le_of_not_ge hend)

/-- An affine priced numerator inherits the positive-part chord at any
actual charge between zero and the endpoint. -/
theorem priced_numerator_chord (b γ offset d ell : ℝ)
    (hell : 0 < ell) (hd : d ∈ Icc (0 : ℝ) ell)
    (hbase : -γ + offset ≤ 0) :
    max (b * d - γ + offset) 0 ≤
      (d / ell) * max (b * ell - γ + offset) 0 := by
  have ht0 : 0 ≤ d / ell := div_nonneg hd.1 hell.le
  have ht1 : d / ell ≤ 1 := (div_le_one₀ hell).2 hd.2
  have heq : (1 - d / ell) * (-γ + offset) +
      (d / ell) * (b * ell - γ + offset) = b * d - γ + offset := by
    field_simp
    ring
  rw [← heq]
  exact positive_part_chord (-γ + offset) (b * ell - γ + offset)
    (d / ell) hbase ht0 ht1

/-- The endpoint numerator is priced with the correct sign before
any reciprocal upper bound is used. -/
theorem endpoint_numerator_le (R e j : ℝ)
    (hj : 0 ≤ j) :
    max (R + e * j) 0 ≤ max R 0 + max e 0 * j := by
  apply max_le
  · have hR : R ≤ max R 0 := le_max_left _ _
    have he : e ≤ max e 0 := le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hj]
  · exact add_nonneg (le_max_right _ _) (mul_nonneg (le_max_right _ _) hj)

theorem endpoint_numerator_le_of_nonpos (R e j : ℝ)
    (hR : R ≤ 0) (hj : 0 ≤ j) :
    max (R + e * j) 0 ≤ max e 0 * j := by
  simpa only [max_eq_right hR, zero_add] using endpoint_numerator_le R e j hj

/-- The same reciprocal and positive-deficit integrals make every
intermediate signed price integrable. -/
theorem integrable_priceFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Set Ω) (a D : Ω → ℝ)
    (A b γ θ ax j v : ℝ)
    (ha : AEStronglyMeasurable a (μ.restrict H))
    (hD : AEStronglyMeasurable D (μ.restrict H))
    (hj : 0 ≤ j)
    (hden : ∀ᵐ h ∂μ.restrict H, 0 < A - a h - ax)
    (hrec : IntegrableOn (fun h => 1 / (A - a h - ax)) H μ)
    (hdef : IntegrableOn (fun h => max (D h - θ) 0 /
      (A - a h - ax)) H μ) :
    IntegrableOn (fun h => max (b * v - γ + (D h - θ) * j) 0 /
      (A - a h - ax)) H μ := by
  have hsm : AEStronglyMeasurable
      (fun h => max (b * v - γ + (D h - θ) * j) 0 /
        (A - a h - ax)) (μ.restrict H) :=
    (continuous_max.comp_aestronglyMeasurable₂
      (aestronglyMeasurable_const.add
        ((hD.sub aestronglyMeasurable_const).mul aestronglyMeasurable_const))
      aestronglyMeasurable_const).div₀
      ((aestronglyMeasurable_const.sub ha).sub aestronglyMeasurable_const)
  apply Integrable.mono'
    ((hrec.const_mul (max (b * v - γ) 0)).add (hdef.const_mul j)) hsm
  filter_upwards [hden] with h hh
  have hnum := endpoint_numerator_le (b * v - γ) (D h - θ) j hj
  have hdiv := div_le_div_of_nonneg_right hnum hh.le
  have hnonneg : 0 ≤ max (b * v - γ + (D h - θ) * j) 0 /
      (A - a h - ax) := div_nonneg (le_max_right _ _) hh.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    _ ≤ (max (b * v - γ) 0 + max (D h - θ) 0 * j) /
      (A - a h - ax) := hdiv
    _ = max (b * v - γ) 0 * (1 / (A - a h - ax)) +
      j * (max (D h - θ) 0 / (A - a h - ax)) := by ring

/-- The signed copy price is convex along the charge interval, and the
proved zero-price margin removes its base endpoint. -/
theorem priceFunction_chord {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Set Ω) (a D : Ω → ℝ)
    (A b γ θ ax j R d ell : ℝ)
    (hell : 0 < ell) (hd : d ∈ Icc (0 : ℝ) ell)
    (hj : 0 ≤ j) (hjR : j ≤ R)
    (hmargin : max (1 - 2 * θ) 0 * R < γ)
    (hpoint : ∀ᵐ h ∂μ.restrict H, D h ≤ 1 - θ ∧ 0 < A - a h - ax)
    (hdint : IntegrableOn (fun h => max (b * d - γ + (D h - θ) * j) 0 /
      (A - a h - ax)) H μ)
    (hellint : IntegrableOn (fun h => max (b * ell - γ + (D h - θ) * j) 0 /
      (A - a h - ax)) H μ) :
    priceFunction μ H a D A b γ θ ax j d ≤
      d / ell * priceFunction μ H a D A b γ θ ax j ell := by
  unfold priceFunction
  have hmono : (∫ h in H, max (b * d - γ + (D h - θ) * j) 0 /
      (A - a h - ax) ∂μ) ≤
      ∫ h in H, d / ell * (max (b * ell - γ + (D h - θ) * j) 0 /
        (A - a h - ax)) ∂μ := by
    apply integral_mono_ae hdint (hellint.const_mul _)
    filter_upwards [hpoint] with h hh
    have hbase : -γ + (D h - θ) * j ≤ 0 := by
      have hz := zero_price_numerator γ θ R (D h) j hh.1 hj hjR hmargin
      have hle := le_max_left (-γ + (D h - θ) * j) 0
      linarith
    have hnum := priced_numerator_chord b γ ((D h - θ) * j) d ell
      hell hd hbase
    have hdiv := div_le_div_of_nonneg_right hnum hh.2.le
    simpa only [div_eq_mul_inv, mul_assoc] using hdiv
  rw [integral_const_mul] at hmono
  exact hmono

/-- One endpoint estimate covers both signs of `b*ell-γ`. A nonpositive
price contributes zero, so it is never multiplied by a reciprocal upper. -/
theorem priceFunction_endpoint_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Set Ω) (a D : Ω → ℝ)
    (A b γ θ ax j ell Irec χ : ℝ)
    (hj : 0 ≤ j)
    (hden : ∀ᵐ h ∂μ.restrict H, 0 < A - a h - ax)
    (hprice : IntegrableOn (fun h => max (b * ell - γ + (D h - θ) * j) 0 /
      (A - a h - ax)) H μ)
    (hrec : IntegrableOn (fun h => 1 / (A - a h - ax)) H μ)
    (hdef : IntegrableOn (fun h => max (D h - θ) 0 /
      (A - a h - ax)) H μ)
    (hrecBound : (∫ h in H, 1 / (A - a h - ax) ∂μ) ≤ Irec)
    (hdefBound : (∫ h in H, max (D h - θ) 0 /
      (A - a h - ax) ∂μ) ≤ χ) :
    priceFunction μ H a D A b γ θ ax j ell ≤
      max (b * ell - γ) 0 * Irec + j * χ := by
  let R := b * ell - γ
  have hmono : priceFunction μ H a D A b γ θ ax j ell ≤
      ∫ h in H, max R 0 * (1 / (A - a h - ax)) +
        j * (max (D h - θ) 0 / (A - a h - ax)) ∂μ := by
    unfold priceFunction
    apply integral_mono_ae hprice ((hrec.const_mul _).add (hdef.const_mul _))
    filter_upwards [hden] with h hh
    have hnum := endpoint_numerator_le R (D h - θ) j hj
    have hdiv := div_le_div_of_nonneg_right hnum hh.le
    change max (R + (D h - θ) * j) 0 / (A - a h - ax) ≤
      max R 0 * (1 / (A - a h - ax)) +
        j * (max (D h - θ) 0 / (A - a h - ax))
    calc
      _ ≤ (max R 0 + max (D h - θ) 0 * j) / (A - a h - ax) := hdiv
      _ = _ := by ring
  rw [integral_add (hrec.const_mul _) (hdef.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  have hrec' := mul_le_mul_of_nonneg_left hrecBound (le_max_right R 0)
  have hdef' := mul_le_mul_of_nonneg_left hdefBound hj
  exact hmono.trans (by simpa only [R] using add_le_add hrec' hdef')

/-- The own-part and outside-own missing allowances spend one common
weighted hole inventory. -/
theorem weighted_hole_inventory_le (ell χ z R N TB Zd : ℝ)
    (hell : 1 / 2 ≤ ell) (hχ : χ ≤ 1 / 2)
    (hZd : 0 ≤ Zd)
    (hown : TB ≤ z * N) (htotal : TB + Zd ≤ R * N) :
    ell * TB + χ * Zd ≤ ((ell - 1 / 2) * z + R / 2) * N := by
  have hχZd := mul_le_mul_of_nonneg_right hχ hZd
  have hown' := mul_le_mul_of_nonneg_left hown (sub_nonneg.mpr hell)
  have htotal' := mul_le_mul_of_nonneg_left htotal (by norm_num : (0:ℝ) ≤ 1/2)
  nlinarith

/-- Integrating the actual copied-row estimate keeps the own-atom and
outside-own missing allowances as separate moments of one source law. -/
theorem integrated_signed_copy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B : Set Ω) (v own j error : Ω → ℝ)
    (A b γ ell P χ : ℝ) (hell : 0 < ell)
    (hv : IntegrableOn v B μ)
    (hown : IntegrableOn (fun x => own x * v x) B μ)
    (hj : IntegrableOn (fun x => v x * j x) B μ)
    (herror : IntegrableOn error B μ)
    (hcopy : ∀ᵐ x ∂μ.restrict B,
      (A - b) * v x - own x * v x + γ ≤
        (P * v x + χ * (v x * j x)) / ell + error x) :
    ell * ((A - b) * (∫ x in B, v x ∂μ) -
      (∫ x in B, own x * v x ∂μ) + γ * μ.real B) ≤
        P * (∫ x in B, v x ∂μ) +
          χ * (∫ x in B, v x * j x ∂μ) +
          ell * (∫ x in B, error x ∂μ) := by
  have hleft : IntegrableOn (fun x => (A - b) * v x - own x * v x + γ) B μ :=
    ((hv.const_mul _).sub hown).add (integrable_const _)
  have hright : IntegrableOn (fun x =>
      (P * v x + χ * (v x * j x)) / ell + error x) B μ := by
    exact (((hv.const_mul P).add (hj.const_mul χ)).div_const ell).add herror
  have hmono := integral_mono_ae hleft hright hcopy
  have hleftEq : (∫ x in B, (A - b) * v x - own x * v x + γ ∂μ) =
      (A - b) * (∫ x in B, v x ∂μ) -
        (∫ x in B, own x * v x ∂μ) + γ * μ.real B := by
    calc
      _ = (∫ x in B, (A - b) * v x - own x * v x ∂μ) +
          (∫ x in B, γ ∂μ) :=
        integral_add ((hv.const_mul _).sub hown) (integrable_const _)
      _ = _ := by
        rw [integral_sub (hv.const_mul _) hown, integral_const_mul,
          setIntegral_const, smul_eq_mul]
        ring
  have hrightEq : (∫ x in B,
      (P * v x + χ * (v x * j x)) / ell + error x ∂μ) =
      (P * (∫ x in B, v x ∂μ) +
        χ * (∫ x in B, v x * j x ∂μ)) / ell +
        (∫ x in B, error x ∂μ) := by
    calc
      _ = (∫ x in B, (P * v x + χ * (v x * j x)) / ell ∂μ) +
          (∫ x in B, error x ∂μ) :=
        integral_add (((hv.const_mul P).add (hj.const_mul χ)).div_const ell) herror
      _ = _ := by
        rw [integral_div, integral_add (hv.const_mul P) (hj.const_mul χ),
          integral_const_mul, integral_const_mul]
  rw [hleftEq, hrightEq] at hmono
  have hscaled := mul_le_mul_of_nonneg_left hmono hell.le
  field_simp [hell.ne'] at hscaled ⊢
  nlinarith only [hscaled]

/-- After the actual two copy bounds have been integrated, the single
weighted inventory forces a strictly positive scalar price in the
nonnegative-price branch. -/
theorem positive_price_necessary (A b γ ell Ecap P χ z R N n TB Zd : ℝ)
    (hell : 1 / 2 < ell) (hγ : 0 < γ) (hE : Ecap < 3 * γ / 5)
    (hN : 0 < N) (hNn : N < ell * n)
    (hχ : χ ≤ 1 / 2) (hZd : 0 ≤ Zd)
    (hown : TB ≤ z * N) (htotal : TB + Zd ≤ R * N)
    (hcopy : ell * ((A - b) * N - TB + γ * n) ≤
      P * N + χ * Zd + ell * Ecap * n) :
    0 < P + (ell - 1 / 2) * z + R / 2 - ell * (A - b) - 2 * γ / 5 := by
  have hprice := weighted_hole_inventory_le ell χ z R N TB Zd hell.le
    hχ hZd hown htotal
  have hq : 0 < 2 * γ / 5 := by linarith
  have hn : 0 < ell * n := lt_of_lt_of_le hN hNn.le
  have hgain : (2 * γ / 5) * N < (γ - Ecap) * (ell * n) := by
    calc
      _ < (2 * γ / 5) * (ell * n) := mul_lt_mul_of_pos_left hNn hq
      _ < (γ - Ecap) * (ell * n) := by
        apply mul_lt_mul_of_pos_right _ hn
        linarith
  have hcombined :
      (ell * (A - b) + 2 * γ / 5) * N <
        (P + (ell - 1 / 2) * z + R / 2) * N := by
    nlinarith [hcopy, hgain, hprice]
  nlinarith [mul_pos hN (sub_pos.mpr hcombined)]

/-- A nonpositive endpoint price, including equality, is incompatible
with a positive original mass gap and the same hole inventory. -/
theorem nonpositive_price_impossible (A b γ ell Ecap χ R N n TB Zd : ℝ)
    (hell : 0 < ell) (hγE : Ecap < γ)
    (hgap : 0 < A - b - R) (hN : 0 < N) (hNn : N < ell * n)
    (hχ : χ ≤ ell) (hZd : 0 ≤ Zd)
    (htotal : TB + Zd ≤ R * N)
    (hcopy : ell * ((A - b) * N - TB + γ * n) ≤
      χ * Zd + ell * Ecap * n) : False := by
  have hn : 0 < n := by nlinarith
  have hweighted : ell * TB + χ * Zd ≤ ell * R * N := by
    have hfirst := mul_le_mul_of_nonneg_right hχ hZd
    have hsecond := mul_le_mul_of_nonneg_left htotal hell.le
    nlinarith
  have hleft : 0 < (A - b - R) * N := mul_pos hgap hN
  have hright : 0 < (γ - Ecap) * n := mul_pos (sub_pos.mpr hγE) hn
  nlinarith [hweighted, hleft, hright]

end Erdos1017.UniversalSignedPrice
