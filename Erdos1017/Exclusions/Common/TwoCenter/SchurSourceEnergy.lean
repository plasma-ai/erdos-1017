module

public import Erdos1017.Exclusions.Common.TwoCenter.SchurHeadPlane

/-!
# Shared-source energy bound from the Schur argument

Isotropic heads, the stationary constant and three source means satisfy the
shared-source energy bound (`source_energy_ge_shared`), with all cone and Schur
signs derived from the index of the form.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.SchurHeadPlane

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Actual isotropic heads, stationary constant and three source means
satisfy the shared-source energy bound. All cone and Schur signs are proved
from the original index and the displayed original Gram entries. -/
theorem source_energy_ge_shared (B : LinearMap.BilinForm ℝ V)
    (hsym : ∀ x y, B x y = B y x) (hindex : PositiveIndexOn B ⊤ 2)
    (a b e c₁ c₂ c₁₂ : V) (ν s₁ s₂ R₁ R₂ : ℝ)
    (hν : 0 < ν) (hκν : 2 * ν ≤ B a b)
    (haa : B a a = 0) (hbb : B b b = 0)
    (hee : B e e = ν) (hea : B e a = ν) (heb : B e b = ν)
    (hec₁ : B e c₁ = ν * s₁) (hec₂ : B e c₂ = ν * s₂)
    (hec₁₂ : 0 < B e c₁₂)
    (ha₁ : B a c₁ = 0) (hb₂ : B b c₂ = 0)
    (ha₁₂ : B a c₁₂ = 0) (hb₁₂ : B b c₁₂ = 0)
    (hq₁ : 0 ≤ B c₁ c₁) (hq₂ : 0 ≤ B c₂ c₂) (hq₁₂ : 0 ≤ B c₁₂ c₁₂)
    (hc₁ : c₁ ≠ 0 → 0 < B c₁₂ c₁) (hc₂ : c₂ ≠ 0 → 0 < B c₁₂ c₂)
    (hr₁ : s₁ ≤ R₁) (hr₂ : s₂ ≤ R₂) :
    B (R₁ • a + R₂ • b - (c₁ + c₂ + c₁₂))
        (R₁ • a + R₂ • b - (c₁ + c₂ + c₁₂)) ≥ B c₁₂ (c₁ + c₂ + c₁₂) := by
  let κ := B a b
  have hκ : 0 < κ := by dsimp only [κ]; linarith
  have hκ0 : B a b ≠ 0 := hκ.ne'
  let w := headResidual B a b e
  let x := headResidual B a b c₁
  let y := headResidual B a b c₂
  let z := headResidual B a b c₁₂
  have hae : B a e = ν := (hsym a e).trans hea
  have hbe : B b e = ν := (hsym b e).trans heb
  have hw : 0 ≤ B w w := by
    have he : B w w = ν - 2 * ν ^ 2 / κ := by
      rw [show w = headResidual B a b e from rfl,
        pairing_headResidual B hsym a b e e haa hbb hκ0, hee, hae, hbe]
      dsimp only [κ]
      ring
    have hle : 2 * ν ^ 2 / κ ≤ ν := (div_le_iff₀ hκ).mpr (by
      have hm := mul_le_mul_of_nonneg_left hκν hν.le
      dsimp only [κ]
      nlinarith only [hm])
    rw [he]
    linarith
  have hx : 0 ≤ B x x := by
    have he := pairing_headResidual B hsym a b c₁ c₁ haa hbb hκ0
    change 0 ≤ B (headResidual B a b c₁) (headResidual B a b c₁)
    rw [he]
    simpa only [ha₁, zero_mul, mul_zero, add_zero, zero_div, sub_zero] using hq₁
  have hy : 0 ≤ B y y := by
    have he := pairing_headResidual B hsym a b c₂ c₂ haa hbb hκ0
    change 0 ≤ B (headResidual B a b c₂) (headResidual B a b c₂)
    rw [he]
    simpa only [hb₂, zero_mul, mul_zero, add_zero, zero_div, sub_zero] using hq₂
  have hz : 0 ≤ B z z := by
    have he := pairing_headResidual B hsym a b c₁₂ c₁₂ haa hbb hκ0
    change 0 ≤ B (headResidual B a b c₁₂) (headResidual B a b c₁₂)
    rw [he]
    simpa only [ha₁₂, hb₁₂, zero_mul, mul_zero, add_zero, zero_div, sub_zero] using hq₁₂
  have hzw : 0 < B z w := by
    have he := pairing_headResidual B hsym a b c₁₂ e haa hbb hκ0
    change 0 < B (headResidual B a b c₁₂) (headResidual B a b e)
    rw [he]
    simpa only [ha₁₂, hb₁₂, zero_mul, add_zero, zero_div, sub_zero,
      hsym c₁₂ e] using hec₁₂
  have hzx : B z x = B c₁₂ c₁ := by
    simpa only [z, x, ha₁₂, hb₁₂, zero_mul, add_zero, zero_div, sub_zero] using
      pairing_headResidual B hsym a b c₁₂ c₁ haa hbb hκ0
  have hzy : B z y = B c₁₂ c₂ := by
    simpa only [z, y, ha₁₂, hb₁₂, zero_mul, add_zero, zero_div, sub_zero] using
      pairing_headResidual B hsym a b c₁₂ c₂ haa hbb hκ0
  have hxzero : c₁ = 0 → x = 0 := by
    intro h
    simp only [x, h, headResidual_zero]
  have hyzero : c₂ = 0 → y = 0 := by
    intro h
    simp only [y, h, headResidual_zero]
  have hwx : 0 ≤ B w x := by
    by_cases hc : c₁ = 0
    · simp only [hxzero hc, map_zero, le_refl]
    · exact residual_pairing_nonnegative_of_common_reference B hsym hindex a b c₁₂ e c₁
        haa hbb hκ hz hw hx hzw (hzx ▸ hc₁ hc)
  have hwy : 0 ≤ B w y := by
    by_cases hc : c₂ = 0
    · simp only [hyzero hc, map_zero, le_refl]
    · exact residual_pairing_nonnegative_of_common_reference B hsym hindex a b c₁₂ e c₂
        haa hbb hκ hz hw hy hzw (hzy ▸ hc₂ hc)
  have hxy : 0 ≤ B x y := by
    by_cases hc : c₁ = 0
    · simp only [hxzero hc, map_zero, LinearMap.zero_apply, le_refl]
    · by_cases hd : c₂ = 0
      · simp only [hyzero hd, map_zero, le_refl]
      · exact residual_pairing_nonnegative_of_common_reference B hsym hindex a b c₁₂ c₁ c₂
          haa hbb hκ hz hx hy (hzx ▸ hc₁ hc) (hzy ▸ hc₂ hd)
  have hzx0 : 0 ≤ B z x := by
    by_cases hc : c₁ = 0
    · simp only [hxzero hc, map_zero, le_refl]
    · exact (hzx ▸ hc₁ hc).le
  have hzy0 : 0 ≤ B z y := by
    by_cases hc : c₂ = 0
    · simp only [hyzero hc, map_zero, le_refl]
    · exact (hzy ▸ hc₂ hc).le
  let U := B a c₂
  let V := B b c₁
  have hwx_eq : B w x = ν * (s₁ - V / κ) := by
    rw [show w = headResidual B a b e from rfl, show x = headResidual B a b c₁ from rfl,
      pairing_headResidual B hsym a b e c₁ haa hbb hκ0, hec₁, hae, hbe, ha₁]
    dsimp only [V, κ]
    ring
  have hwy_eq : B w y = ν * (s₂ - U / κ) := by
    rw [show w = headResidual B a b e from rfl, show y = headResidual B a b c₂ from rfl,
      pairing_headResidual B hsym a b e c₂ haa hbb hκ0, hec₂, hae, hbe, hb₂]
    dsimp only [U, κ]
    ring
  have hV : V ≤ κ * s₁ := by
    have hdiv : V / κ ≤ s₁ := by
      apply (mul_le_mul_iff_right₀ hν).mp
      rw [hwx_eq] at hwx
      nlinarith only [hwx]
    simpa only [mul_comm] using (div_le_iff₀ hκ).mp hdiv
  have hU : U ≤ κ * s₂ := by
    have hdiv : U / κ ≤ s₂ := by
      apply (mul_le_mul_iff_right₀ hν).mp
      rw [hwy_eq] at hwy
      nlinarith only [hwy]
    simpa only [mul_comm] using (div_le_iff₀ hκ).mp hdiv
  have hleft : 0 ≤ κ * R₁ - V := by nlinarith only [hV, mul_le_mul_of_nonneg_left hr₁ hκ.le]
  have hright : 0 ≤ κ * R₂ - U := by nlinarith only [hU, mul_le_mul_of_nonneg_left hr₂ hκ.le]
  let C := c₁ + c₂ + c₁₂
  have hres : B c₁₂ C ≤ B (headResidual B a b C) (headResidual B a b C) := by
    have hzz : B z z = B c₁₂ c₁₂ := by
      simpa only [z, ha₁₂, hb₁₂, zero_mul, add_zero, zero_div, sub_zero] using
        pairing_headResidual B hsym a b c₁₂ c₁₂ haa hbb hκ0
    have he : B (headResidual B a b C) (headResidual B a b C) =
        B x x + B y y + B z z + 2 * B x y + 2 * B z x + 2 * B z y := by
      simp only [C, headResidual_add, show headResidual B a b c₁ = x from rfl,
        show headResidual B a b c₂ = y from rfl,
        show headResidual B a b c₁₂ = z from rfl,
        map_add, LinearMap.add_apply, hsym y x, hsym x z, hsym y z]
      ring
    rw [he]
    change B c₁₂ (c₁ + c₂ + c₁₂) ≤ _
    simp only [map_add]
    rw [← hzx, ← hzy, ← hzz]
    linarith only [hx, hy, hxy, hzx0, hzy0]
  have henergy : B (R₁ • a + R₂ • b - C) (R₁ • a + R₂ • b - C) =
      B (headResidual B a b C) (headResidual B a b C) +
        2 * (κ * R₁ - V) * (κ * R₂ - U) / κ := by
    rw [pairing_headResidual B hsym a b C C haa hbb hκ0]
    simp only [C, map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, haa, hbb, ha₁, hb₂, ha₁₂, hb₁₂,
      hsym b a, hsym c₁ a, hsym c₁ b, hsym c₂ a, hsym c₂ b, hsym c₁₂ a, hsym c₁₂ b]
    dsimp only [U, V, κ]
    field_simp [hκ0]
    ring
  have hproduct : 0 ≤ 2 * (κ * R₁ - V) * (κ * R₂ - U) / κ := by positivity
  change B c₁₂ C ≤ B (R₁ • a + R₂ • b - C) (R₁ • a + R₂ • b - C)
  rw [henergy]
  linarith only [hproduct, hres]

end Erdos1017.SchurHeadPlane
