module

public import Erdos1017.Exclusions.E2.Middle.UniversalIntegratedDeficitFloor

/-!
# Refined deficit floor from tangent and integrated rows

The integrated triangle rows and a tangent floor on positive missing sections
refine the complete-part bound, the tangent and integrated-row floors bound the
same weighted missing integral, and one shared joint budget with the refined
weighted floor gives the necessary square inequality
(`refined_joint_necessary`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.UniversalDeficit

/-- The integrated triangle rows and a tangent floor on positive missing
sections refine the complete-part bound. Zero sections, including genuine
dust, remain in the same integral. -/
theorem refined_complete_part_lower
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (D a : Ω → ℝ) (hD : Integrable D ν) {δ C t₀ : ℝ} (hδ : 0 < δ)
    (hrows : ∀ᵐ x ∂ν, 0 ≤ D x ∧ a x ≤ C ∧
      δ * (ν.real univ - a x) ≤
        (ν.real univ - 2 * a x) * D x + ∫ y, D y ∂ν)
    (htangent : ∀ᵐ x ∂ν, 0 < a x → δ * t₀ ≤ D x) :
    min (ν.real univ / 2)
      (ν.real univ - C + (2 * C - ν.real univ) * min (1 / 2) t₀) ≤
        (∫ y, D y ∂ν) / δ := by
  apply (le_div_iff₀ hδ).mpr
  by_cases hhalf : ∀ᵐ x ∂ν, δ / 2 ≤ D x
  · have hi := integral_mono_ae (integrable_const (δ / 2)) hD hhalf
    simp only [integral_const, smul_eq_mul] at hi
    have hm := mul_le_mul_of_nonneg_right
      (min_le_left (ν.real univ / 2)
        (ν.real univ - C + (2 * C - ν.real univ) * min (1 / 2) t₀)) hδ.le
    nlinarith only [hi, hm]
  · have hex : ∃ x, (0 ≤ D x ∧ a x ≤ C ∧
        δ * (ν.real univ - a x) ≤
          (ν.real univ - 2 * a x) * D x + ∫ y, D y ∂ν) ∧
        (0 < a x → δ * t₀ ≤ D x) ∧ ¬ δ / 2 ≤ D x := by
      by_contra hn
      push Not at hn
      exact hhalf ((hrows.and htangent).mono fun x hx => hn x hx.1 hx.2)
    obtain ⟨x, hx, ht, hl⟩ := hex
    have hlt : D x < δ / 2 := lt_of_not_ge hl
    by_cases ha : a x ≤ ν.real univ / 2
    · have hp := mul_le_mul_of_nonneg_left hlt.le
        (by linarith : 0 ≤ ν.real univ - 2 * a x)
      have hm := mul_le_mul_of_nonneg_right
        (min_le_left (ν.real univ / 2)
          (ν.real univ - C + (2 * C - ν.real univ) * min (1 / 2) t₀)) hδ.le
      nlinarith only [hx.2.2, hp, hm]
    · have hapos : 0 < a x := by
        have hη : 0 ≤ ν.real univ := measureReal_nonneg
        linarith
      have htlow : δ * min (1 / 2) t₀ ≤ D x :=
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le).trans (ht hapos)
      have hp := mul_le_mul_of_nonneg_left htlow
        (by linarith : 0 ≤ 2 * a x - ν.real univ)
      have hmove := mul_nonneg (sub_nonneg.mpr hx.2.1)
        (show 0 ≤ 1 - 2 * min (1 / 2 : ℝ) t₀ by linarith [min_le_left (1 / 2 : ℝ) t₀])
      have hmoveδ := mul_nonneg hδ.le hmove
      have hm := mul_le_mul_of_nonneg_right
        (min_le_right (ν.real univ / 2)
          (ν.real univ - C + (2 * C - ν.real univ) * min (1 / 2) t₀)) hδ.le
      nlinarith only [hx.2.2, hp, hmoveδ, hm]

/-- The tangent and integrated-row floors bound the same weighted missing
integral. No lower bound is imposed on zero missing sections. -/
theorem refined_weighted_atomic_floor
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (D a : Ω → ℝ) (hD : Integrable D ν) (ha : Integrable a ν)
    (haD : Integrable (fun x => a x * D x) ν)
    {δ C p t₀ : ℝ} (hδ : 0 < δ)
    (hrows : ∀ᵐ x ∂ν, 0 ≤ D x ∧ a x ≤ C ∧
      δ * (ν.real univ - a x) ≤
        (ν.real univ - 2 * a x) * D x + ∫ y, D y ∂ν)
    (hanonneg : ∀ᵐ x ∂ν, 0 ≤ a x)
    (htangent : ∀ᵐ x ∂ν, 0 < a x → δ * t₀ ≤ D x)
    (hcap : (∫ y, D y ∂ν) ≤ δ * p) :
    let tf := if 0 < ν.real univ - 2 * C then
      max t₀ (max 0 ((ν.real univ - C - p) / (ν.real univ - 2 * C))) else t₀
    δ * tf * (∫ x, a x ∂ν) ≤ ∫ x, a x * D x ∂ν := by
  dsimp only
  let tf := if 0 < ν.real univ - 2 * C then
    max t₀ (max 0 ((ν.real univ - C - p) / (ν.real univ - 2 * C))) else t₀
  have hpoint : ∀ᵐ x ∂ν, δ * tf * a x ≤ a x * D x := by
    filter_upwards [hrows, hanonneg, htangent] with x hx hax ht
    by_cases hpos : 0 < a x
    · have hfloor : δ * tf ≤ D x := by
        dsimp only [tf]
        split_ifs with hden
        · have hlower := complete_part_lower_of_integrated_rows D a hD hδ hrows
          have hC : C < ν.real univ / 2 := by linarith
          have hp : ν.real univ / 2 ≤ p := by
            rw [min_eq_left (by linarith)] at hlower
            exact (mul_le_mul_iff_right₀ hδ).mp (hlower.trans hcap)
          have hf := uniform_atomic_floor hδ hp hC hx.2.1 hx.2.2 hcap
          rw [mul_max_of_nonneg _ _ hδ.le, mul_max_of_nonneg _ _ hδ.le]
          apply max_le (ht hpos)
          apply max_le (by simpa using hx.1)
          simpa only [mul_div_assoc] using hf
        · exact ht hpos
      simpa only [mul_comm (a x)] using mul_le_mul_of_nonneg_right hfloor hax
    · have hz : a x = 0 := le_antisymm (le_of_not_gt hpos) hax
      simp [hz]
  have hi := integral_mono_ae (ha.const_mul (δ * tf)) haD hpoint
  rw [integral_const_mul] at hi
  exact hi

/-- One shared joint budget and the refined weighted floor give the
necessary square inequality, including the case where its coefficient
is negative and the atomic term is simply discarded. -/
theorem refined_joint_necessary {η u A δ p DH Q T L Qcap tf : ℝ}
    (hδ : 0 < δ) (hcoef : 0 ≤ η + u - A) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hcap : DH ≤ δ * p) (hQcap : Q ≤ Qcap) (hfloor : δ * tf * Q ≤ T)
    (hjoint : δ * (η ^ 2 - Q + L) + 2 * T ≤ η * (δ * p) + (η + u - A) * DH) :
    η ^ 2 - max (1 - 2 * tf) 0 * Qcap ≤ (2 * η + u - A) * p := by
  have hc := mul_le_mul_of_nonneg_left hcap hcoef
  have hpaid : δ * (η ^ 2 - (1 - 2 * tf) * Q + L - (2 * η + u - A) * p) ≤ 0 := by
    nlinarith only [hjoint, hc, hfloor]
  have hbase := nonpos_of_mul_nonpos_right hpaid hδ
  have hscale := mul_le_mul_of_nonneg_left hQcap (le_max_right (1 - 2 * tf) 0)
  have hmax := mul_le_mul_of_nonneg_right (le_max_left (1 - 2 * tf) 0) hQ
  nlinarith only [hbase, hL, hscale, hmax]

end Erdos1017.UniversalDeficit
