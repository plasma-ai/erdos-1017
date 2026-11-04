module

public import Erdos1017.Multipartite.MultipartiteDustStationarity
public import Erdos1017.Multipartite.MultipartiteCompletionVariation
public import Erdos1017.Multipartite.Countable.CountableEuler

/-!
# The gamma formula from stationary rows

The countable Euler identity converts the selected multiplier's stationary rows
into the physical gamma formula, with or without dust, and in the head-count
regime the repeat bound gives a multiplier below one, so this gamma is positive.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The actual countable Euler identity converts the selected multiplier's
stationary rows into the physical gamma formula, with or without dust. -/
theorem gamma_identity_of_head_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i : ℕ) (hi : 0 < x.2 i) :
    (anchorRow x.2 (MultipartiteProfiles.dust x) D - ℓ) / (1 + x.1) =
      2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε) := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx.1
  have hsqsum := MultipartiteProfiles.squares_summable hx.1
  let R := anchorRow x.2 (MultipartiteProfiles.dust x) D
  have hterm (k : ℕ) : x.2 k * headRow x.2 (MultipartiteProfiles.dust x) D k =
      (R - ℓ) * x.2 k + ℓ * (x.2 k) ^ 2 := by
    by_cases hk : 0 < x.2 k
    · have h := hrows k hk
      change headRow x.2 (MultipartiteProfiles.dust x) D k - R = ℓ * (x.2 k - 1) at h
      nlinarith
    · have hk0 : x.2 k = 0 := le_antisymm (le_of_not_gt hk) (hp k)
      simp [hk0]
  have hhead : (∑' k, x.2 k * headRow x.2 (MultipartiteProfiles.dust x) D k) =
      (R - ℓ) * (∑' k, x.2 k) + ℓ * (∑' k, (x.2 k) ^ 2) := by
    rw [tsum_congr hterm, (hsum.mul_left (R - ℓ)).tsum_add (hsqsum.mul_left ℓ),
      tsum_mul_left, tsum_mul_left]
  have hdust : MultipartiteProfiles.dust x * dustRow x.2 (MultipartiteProfiles.dust x) D =
      MultipartiteProfiles.dust x * (R - ℓ) := by
    by_cases hs0 : MultipartiteProfiles.dust x = 0
    · simp [hs0]
    · have hs : 0 < MultipartiteProfiles.dust x :=
        lt_of_le_of_ne (MultipartiteProfiles.dust_nonneg hx.1) (Ne.symm hs0)
      rw [dust_row_of_head_multiplier hε hx hmax hxvalue hD hopt ℓ hrows i hi hs]
  have heuler := row_euler hD x.2 hp hsum (MultipartiteProfiles.dust x)
  rw [hhead, hdust, hopt] at heuler
  have hT : MultipartiteProfiles.dust x + (∑' k, x.2 k) = x.1 := by
    rw [MultipartiteProfiles.dust_eq_sub_tsum hx.1]
    ring
  have hTweighted := congrArg (fun z : ℝ => (R - ℓ) * z) hT
  have heuler' : R + (R - ℓ) * x.1 + ℓ * (∑' k, (x.2 k) ^ 2) =
      2 * MultipartiteProfiles.limitValue x := by
    change R + ((R - ℓ) * (∑' k, x.2 k) + ℓ * (∑' k, (x.2 k) ^ 2)) +
      MultipartiteProfiles.dust x * (R - ℓ) = _ at heuler
    nlinarith [hTweighted]
  have hmoment : 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
  have hmomentℓ := congrArg (fun z : ℝ => ℓ * z) hmoment
  have hden : 0 < 1 + x.1 := by linarith [hx.1.1.1.1]
  change (R - ℓ) / (1 + x.1) = _
  unfold MultipartiteProfiles.normalizedValue
  field_simp [hden.ne']
  nlinarith [hmomentℓ, heuler']

/-- In the head-count regime the actual repeat bound gives a multiplier
below one, so the gamma determined by stationary rows is positive. -/
theorem positive_gamma_of_half_lt_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ)
    (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i : ℕ) (hi : 0 < x.2 i) (hti : head D i < 1) :
    ℓ < 1 ∧ 0 < 2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε) ∧
      (anchorRow x.2 (MultipartiteProfiles.dust x) D - ℓ) / (1 + x.1) =
        2 * (MultipartiteProfiles.normalizedValue x - ℓ * ε) := by
  have hbound := twoRepeat_bounds_of_half_lt_multiplier hε hx hmax hxvalue hD hopt ℓ hℓ i hi hti (hrows i hi)
  refine ⟨hbound.2.2, ?_, gamma_identity_of_head_multiplier hε hx hmax hxvalue hD hopt ℓ hrows i hi⟩
  nlinarith [mul_pos hε (sub_pos.mpr hbound.2.2)]

end Erdos1017.MultipartiteCountableDual
