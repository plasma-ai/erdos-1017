module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrated deficit floor and its three polynomials

The complete-part lower bound follows from the integrated triangle rows, a cap
strictly below the remaining mass selects the half-mass branch, and one joint
budget with two square caps gives the three necessary polynomials including the
boundary `z = 0` (`three_polynomials`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.UniversalDeficit

/-- The complete-part lower bound follows directly from the integrated
triangle rows. The zero-missing-mass dust is included in the same integral. -/
theorem complete_part_lower_of_integrated_rows
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (D a : Ω → ℝ) (hD : Integrable D ν) {δ C : ℝ} (hδ : 0 < δ)
    (hrows : ∀ᵐ x ∂ν, 0 ≤ D x ∧ a x ≤ C ∧
      δ * (ν.real univ - a x) ≤
        (ν.real univ - 2 * a x) * D x + ∫ y, D y ∂ν) :
    δ * min (ν.real univ / 2) (ν.real univ - C) ≤ ∫ y, D y ∂ν := by
  by_cases hhalf : ∀ᵐ x ∂ν, δ / 2 ≤ D x
  · have h := integral_mono_ae (integrable_const (δ / 2)) hD hhalf
    simp only [integral_const, smul_eq_mul] at h
    have hh := mul_le_mul_of_nonneg_left
      (min_le_left (ν.real univ / 2) (ν.real univ - C)) hδ.le
    linarith
  · have hex : ∃ x, (0 ≤ D x ∧ a x ≤ C ∧
        δ * (ν.real univ - a x) ≤
          (ν.real univ - 2 * a x) * D x + ∫ y, D y ∂ν) ∧ ¬ δ / 2 ≤ D x := by
      by_contra hn
      push Not at hn
      exact hhalf (hrows.mono hn)
    obtain ⟨x, hx, hl⟩ := hex
    have hlt : D x < δ / 2 := lt_of_not_ge hl
    by_cases ha : a x ≤ ν.real univ / 2
    · have hp := mul_le_mul_of_nonneg_left hlt.le (by linarith : 0 ≤ ν.real univ - 2 * a x)
      have hm := mul_le_mul_of_nonneg_left
        (min_le_left (ν.real univ / 2) (ν.real univ - C)) hδ.le
      nlinarith only [hx.2.2, hp, hm]
    · have hp := mul_nonpos_of_nonpos_of_nonneg
        (by linarith : ν.real univ - 2 * a x ≤ 0) hx.1
      have hc := mul_le_mul_of_nonneg_left hx.2.1 hδ.le
      have hm := mul_le_mul_of_nonneg_left
        (min_le_right (ν.real univ / 2) (ν.real univ - C)) hδ.le
      nlinarith only [hx.2.2, hp, hc, hm]

/-- A cap strictly below the remaining mass selects the half-mass branch. -/
theorem floor_domain {η C p δ D : ℝ} (hδ : 0 < δ)
    (hmin : δ * min (η / 2) (η - C) ≤ D) (hcap : D ≤ δ * p)
    (hN : 0 < η - C - p) : η / 2 ≤ p ∧ C < η / 2 := by
  have hle : min (η / 2) (η - C) ≤ p :=
    (mul_le_mul_iff_right₀ hδ).mp (hmin.trans hcap)
  have hp : η / 2 ≤ p := by
    by_contra hn
    have hm : p < min (η / 2) (η - C) := lt_min (lt_of_not_ge hn) (by linarith)
    exact (not_lt_of_ge hle) hm
  exact ⟨hp, by linarith⟩

/-- The atomic floor is uniform over every actual part below the cap. -/
theorem uniform_atomic_floor {η C p δ D a DH : ℝ}
    (hδ : 0 < δ) (hp : η / 2 ≤ p) (hC : C < η / 2) (ha : a ≤ C)
    (hrow : δ * (η - a) ≤ (η - 2 * a) * D + DH)
    (hcap : DH ≤ δ * p) : δ * (η - C - p) / (η - 2 * C) ≤ D := by
  have hden : 0 < η - 2 * C := by linarith
  have haden : 0 < η - 2 * a := by linarith
  apply (div_le_iff₀ hden).mpr
  have hscaled := mul_le_mul_of_nonneg_left
    (show δ * (η - a - p) ≤ (η - 2 * a) * D by linarith) hden.le
  have hmono := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 2 * p - η by linarith)
  have hm := mul_nonneg hδ.le hmono
  have hprod : (η - 2 * a) * (δ * (η - C - p) - D * (η - 2 * C)) ≤ 0 := by
    nlinarith only [hscaled, hm]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hprod haden)

/-- One shared joint budget and two alternative square caps give the
three necessary polynomials, including the boundary z = 0. -/
theorem three_polynomials {A b η u y h C δ DH Q T L : ℝ}
    (hδ : 0 < δ) (hmass : A + b + η + u = 1) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hp : η / 2 ≤ y - u) (_hC : C < η / 2)
    (hN : 0 < η - C - (y - u)) (hcoef : 0 ≤ η + u - A)
    (hcap : DH ≤ δ * (y - u))
    (hfloor : δ * Q * (η - C - (y - u)) / (η - 2 * C) ≤ T)
    (hjoint : δ * (η ^ 2 - Q + L) + 2 * T ≤ η * (δ * (y - u)) + (η + u - A) * DH)
    (hQC : Q ≤ C * η) (hQh : Q ≤ h - A ^ 2 - b ^ 2 - 2 * b * η) :
    0 ≤ h - A ^ 2 - b ^ 2 - 2 * b * η ∧
      0 ≤ (2 * (y - u) - η) * C * η -
        ((1 - A - b - y) ^ 2 - (y - A) * (y - u)) * (η - 2 * C) ∧
      0 ≤ (2 * (y - u) - η) * (h - A ^ 2 - b ^ 2 - 2 * b * η) -
        ((1 - A - b - y) ^ 2 - (y - A) * (y - u)) * (η - 2 * C) := by
  have hden : 0 < η - 2 * C := by linarith
  have hz : 0 ≤ 2 * (y - u) - η := by linarith
  have hfloor' := (div_le_iff₀ hden).mp hfloor
  have hc := mul_le_mul_of_nonneg_left hcap hcoef
  have hupper : δ * (η ^ 2 - Q + L) + 2 * T ≤
      η * (δ * (y - u)) + (η + u - A) * (δ * (y - u)) := by linarith only [hjoint, hc]
  have hj := mul_le_mul_of_nonneg_left hupper hden.le
  have heq : (1 - A - b - y) ^ 2 - (y - A) * (y - u) = η ^ 2 - (2 * η + u - A) * (y - u) := by
    have he : 1 - A - b - y = η - (y - u) := by linarith only [hmass]
    rw [he]
    ring
  have hpaid : δ * (((1 - A - b - y) ^ 2 - (y - A) * (y - u) + L) * (η - 2 * C) -
      (2 * (y - u) - η) * Q) ≤ 0 := by
    rw [heq]
    nlinarith only [hj, hfloor']
  have hbase := nonpos_of_mul_nonpos_right hpaid hδ
  have hdrop := mul_nonneg hL hden.le
  have hfirst := mul_le_mul_of_nonneg_left hQC hz
  have hsecond := mul_le_mul_of_nonneg_left hQh hz
  exact ⟨hQ.trans hQh, by nlinarith only [hbase, hdrop, hfirst],
    by nlinarith only [hbase, hdrop, hsecond]⟩

end Erdos1017.UniversalDeficit
