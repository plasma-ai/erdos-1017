module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Scalar shared-mass bound

The reverse budget and the shared-source energy credit force the sharp
shared-mass bound, with the endpoint height and intercept kept explicit.
-/

@[expose] public section

namespace Erdos1017.TwoCenterSharedMassBound

/-- The actual reverse budget and the paid original shared-source energy
credit force the sharp shared-mass bound. The endpoint height and old
intercept are explicit; no contact or energy hypothesis is suppressed. -/
theorem shared_mass_lt (ell gamma t u E : ℝ)
    (hell : ell ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) (hu : 0 ≤ u)
    (hgamma : (1 - ell) / 4 < gamma) (hE : 0 ≤ E)
    (hshared : u * (2 * (1 + ell) * t - 1 + gamma) ≤ E)
    (hbudget : gamma + E ≤ 2 * (1 - ell) * t ^ 2) :
    u < (1 - ell) / (4 * ell) := by
  let δ := 1 - ell
  let ν := gamma + ell
  let L := 2 * (1 + ell) * t - 1 + gamma
  let C := 2 * δ * t ^ 2 - gamma
  let D := δ / 2 - gamma
  have hell0 : 0 < ell := by linarith [hell.1]
  have hδ : 0 < δ := by dsimp only [δ]; linarith [hell.2]
  have hγ : δ / 4 < gamma := hgamma
  have hγ0 : 0 < gamma := lt_trans (by positivity : (0 : ℝ) < δ / 4) hγ
  have hν : 0 < ν := add_pos hγ0 hell0
  have hνell : ell ≤ ν := by dsimp only [ν]; linarith only [hγ0]
  have htSq : (1 / 8 : ℝ) < t ^ 2 := by
    apply (mul_lt_mul_iff_right₀ hδ).mp
    change δ * (1 / 8) < δ * t ^ 2
    have hb : gamma + E ≤ 2 * δ * t ^ 2 := hbudget
    nlinarith only [hγ, hb, hE]
  have htThird : (1 / 3 : ℝ) < t := by
    by_contra hn
    have hle : t ≤ 1 / 3 := le_of_not_gt hn
    have hs := mul_self_le_mul_self ht0 hle
    nlinarith only [htSq, hs]
  have hL : 0 < L := by
    have hm := mul_pos (by linarith [hell.1] : 0 < 2 * (1 + ell)) (sub_pos.mpr htThird)
    dsimp only [L, δ] at *
    nlinarith only [hm, hgamma, hell.1]
  have hC : u * L ≤ C := by
    dsimp only [C, δ, L]
    linarith only [hshared, hbudget]
  have hbracket : 0 < 2 * δ * ν * t - δ + gamma * (3 + ell) := by
    have h1 := mul_nonneg (by positivity : 0 ≤ 2 * δ * ν) (sub_pos.mpr htThird).le
    have h2 := mul_nonneg (by positivity : 0 ≤ 2 * δ / 3) (sub_nonneg.mpr hνell)
    have h3 := mul_pos (sub_pos.mpr hγ) (by linarith [hell.1] : 0 < 3 + ell)
    have h4 := mul_pos hδ (by linarith [hell.1] : 0 < 11 * ell - 3)
    nlinarith only [h1, h2, h3, h4]
  have hid : D * L - ν * C =
      (1 / 2 - t) * (2 * δ * ν * t - δ + gamma * (3 + ell)) := by
    dsimp only [D, L, C, ν, δ]
    ring
  have hbound : ν * C ≤ D * L := by
    have hp := mul_nonneg (sub_nonneg.mpr htHalf) hbracket.le
    linarith only [hid, hp]
  have huν : u * ν ≤ D := by
    apply (mul_le_mul_iff_right₀ hL).mp
    have hm := mul_le_mul_of_nonneg_left hC hν.le
    nlinarith only [hm, hbound]
  have hD : D < δ / 4 := by dsimp only [D]; linarith only [hγ]
  have huell : u * ell ≤ u * ν := mul_le_mul_of_nonneg_left hνell hu
  apply (lt_div_iff₀ (by positivity : 0 < 4 * ell)).mpr
  change u * (4 * ell) < δ
  linarith only [huell, huν, hD]

end Erdos1017.TwoCenterSharedMassBound
