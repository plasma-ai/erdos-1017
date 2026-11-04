module

public import Erdos1017.Multipartite.Dust.CountableDustVariation

/-!
# Stationarity of the dust row

Positive dust permits two-sided transfers between a head and dust, balanced at
the anchor with exact original density, and these transfers identify the dust
row with the regular multiplier already determined by the positive head rows.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Positive dust permits actual two-sided transfers between a head and
dust, balanced at the anchor and with exact original density. -/
theorem head_dust_transfer_local_max {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    ∃ η : ℝ, 0 < η ∧ ∀ t r : ℝ, |t| < η → |r| < η →
      2 * (x.2 i - 1) * t - 2 * r + 2 * t ^ 2 + 2 * t * r + r ^ 2 = 0 →
      t * (headRow x.2 (MultipartiteProfiles.dust x) D i -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) +
        r * (dustRow x.2 (MultipartiteProfiles.dust x) D -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) - head D i * t ^ 2 -
        (linear D + penalty D / 2) * r ^ 2 - (incident D i + head D i + linear D) * t * r ≤ 0 := by
  have hp : ∀ k, 0 ≤ x.2 k := hx.1.1.1.2
  have hsum := MultipartiteProfiles.atoms_summable hx.1
  have hsqsum := MultipartiteProfiles.squares_summable hx.1
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  let b := Real.sqrt (∑' k, (x.2 k) ^ 2)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = ∑' k, (x.2 k) ^ 2 := Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg _)
  have hb1 : b < 1 := by nlinarith
  have hpb (k : ℕ) : x.2 k ≤ b := by
    have hk := hsqsum.le_tsum k (fun _ _ => sq_nonneg _)
    nlinarith [hp k]
  let η := min (x.2 i / 2) (min (MultipartiteProfiles.dust x / 2) ((1 - b) / 4))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hηi : η ≤ x.2 i / 2 := min_le_left _ _
  have hηs : η ≤ MultipartiteProfiles.dust x / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η ≤ (1 - b) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, ?_⟩
  intro t r ht hr hconstraint
  have ht' := abs_lt.mp ht
  have hr' := abs_lt.mp hr
  have hti : 0 ≤ x.2 i + t := by linarith
  have hsr : 0 ≤ MultipartiteProfiles.dust x + r := by linarith
  have ha : 0 < 1 - t - r := by linarith
  let p := Function.update x.2 i (x.2 i + t)
  have hp' (k : ℕ) : 0 ≤ p k := by
    by_cases hk : k = i
    · subst k
      simpa [p] using hti
    · simpa [p, Function.update_of_ne, hk] using hp k
  have hp1' (k : ℕ) : p k ≤ 1 - t - r := by
    by_cases hk : k = i
    · subst k
      simp only [p, Function.update_self]
      linarith [hpb i]
    · simp only [p, Function.update_of_ne hk]
      linarith [hpb k]
  have hpsum : (∑' k, p k) = (∑' k, x.2 k) + t := by
    rw [show p = Function.update x.2 i (x.2 i + t) from rfl,
      (hsum.hasSum.update i (x.2 i + t)).tsum_eq]
    ring
  have htotal : 1 - t - r + (MultipartiteProfiles.dust x + r) + (∑' k, p k) = 1 + x.1 := by
    rw [hpsum, MultipartiteProfiles.dust_eq_sub_tsum hx.1]
    ring
  have hmoment : (1 - t - r) ^ 2 + (∑' k, (p k) ^ 2) =
      2 * ε * (1 - t - r + (MultipartiteProfiles.dust x + r) + ∑' k, p k) ^ 2 := by
    rw [htotal, show p = Function.update x.2 i (x.2 i + t) from rfl,
      square_tsum_update x.2 hsqsum i t]
    have hold : 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
    nlinarith
  have hraw := physicalObjective_le_density_maximum hε hmax hxvalue.le (1 - t - r) ha
    p hp' hp1' (hsum.update i _) (MultipartiteProfiles.dust x + r) hsr hmoment hD
  rw [htotal] at hraw
  have hden : 0 < (1 + x.1) ^ 2 := by
    have hx0 : 0 ≤ x.1 := hx.1.1.1.1
    positivity
  have hbound := (div_le_div_iff_of_pos_right hden).mp hraw
  rw [show p = Function.update x.2 i (x.2 i + t) from rfl,
    physicalObjective_head_dust_transfers hD x.2 hp hsum (MultipartiteProfiles.dust x) i t r hti,
    hopt] at hbound
  linarith

/-- Actual positive-dust transfers identify the dust row with the same
regular multiplier already determined by the positive head rows. -/
theorem dust_transfer_condition {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    (dustRow x.2 (MultipartiteProfiles.dust x) D - anchorRow x.2 (MultipartiteProfiles.dust x) D) *
        (x.2 i - 1) =
      -(headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D) := by
  let ci := headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D
  let cd := dustRow x.2 (MultipartiteProfiles.dust x) D - anchorRow x.2 (MultipartiteProfiles.dust x) D
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  have hsqsum := MultipartiteProfiles.squares_summable hx.1
  have hpi : x.2 i < 1 := by
    have hiQ := hsqsum.le_tsum i (fun _ _ => sq_nonneg _)
    nlinarith
  have hpi0 : x.2 i - 1 ≠ 0 := by linarith
  let ρ := (-1) / (x.2 i - 1)
  have hρ : ρ * (x.2 i - 1) = -1 := div_mul_cancel₀ _ hpi0
  obtain ⟨η, hη, hlocal⟩ := head_dust_transfer_local_max hε hx hmax hxvalue hD hopt i hi hs
  let η' := η / (|ρ| + 2)
  have hη' : 0 < η' := div_pos hη (by positivity)
  have hηeq : η' * (|ρ| + 2) = η :=
    div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < |ρ| + 2))
  have hηle : η' ≤ η := div_le_self hη.le (by linarith [abs_nonneg ρ])
  have hconditions := Variation.lagrange_tangent_conditions_of_local_max
    (2 * ρ ^ 2 - 2 * ρ + 1) (2 * (1 - x.2 i)) (2 * ρ - 1) 2
    (cd - ρ * ci) (-ci)
    (-head D i * ρ ^ 2 - (linear D + penalty D / 2) + ρ * (incident D i + head D i + linear D))
    ((-2 * ρ * head D i + (incident D i + head D i + linear D)) / 2) (-head D i)
    (by linarith) η' hη' (by
      intro t r ht hr hroot
      have hut : |-(ρ * t) - r| < η := by
        have htri := abs_sub (-(ρ * t)) r
        rw [abs_neg, abs_mul] at htri
        have hprod := mul_le_mul_of_nonneg_left ht.le (abs_nonneg ρ)
        nlinarith
      have hvt : |t| < η := ht.trans_le hηle
      have hconstraint : 2 * (x.2 i - 1) * (-(ρ * t) - r) - 2 * t +
          2 * (-(ρ * t) - r) ^ 2 + 2 * (-(ρ * t) - r) * t + t ^ 2 = 0 := by
        have hρt := congrArg (fun z : ℝ => z * t) hρ
        nlinarith [hroot]
      have h := hlocal (-(ρ * t) - r) t hut hvt hconstraint
      change (-(ρ * t) - r) * ci + t * cd - head D i * (-(ρ * t) - r) ^ 2 -
        (linear D + penalty D / 2) * t ^ 2 -
        (incident D i + head D i + linear D) * (-(ρ * t) - r) * t ≤ 0 at h
      convert h using 1
      ring)
  change cd * (x.2 i - 1) = -ci
  have h := hconditions.1
  dsimp [ρ] at h
  field_simp [hpi0] at h
  nlinarith

/-- The selected head multiplier is stationary on positive dust as well. -/
theorem dust_row_of_head_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    dustRow x.2 (MultipartiteProfiles.dust x) D = anchorRow x.2 (MultipartiteProfiles.dust x) D - ℓ := by
  have hcondition := dust_transfer_condition hε hx hmax hxvalue hD hopt i hi hs
  have hrow := hrows i hi
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  have hiQ := (MultipartiteProfiles.squares_summable hx.1).le_tsum i (fun _ _ => sq_nonneg _)
  have hi0 : x.2 i - 1 ≠ 0 := by nlinarith
  have heq : (dustRow x.2 (MultipartiteProfiles.dust x) D - anchorRow x.2 (MultipartiteProfiles.dust x) D) *
      (x.2 i - 1) = (-ℓ) * (x.2 i - 1) := by nlinarith
  have h := mul_right_cancel₀ hi0 heq
  linarith

end Erdos1017.MultipartiteCountableDual
