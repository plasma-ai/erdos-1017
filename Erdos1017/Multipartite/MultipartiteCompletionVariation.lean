module

public import Erdos1017.Multipartite.Countable.CountablePhysicalCompletion
public import Erdos1017.Multipartite.Countable.CountableRepeatHalf
public import Erdos1017.Multipartite.RightQuadraticConstraint

/-!
# Completion as a one-sided local maximum

Completing a positive head mass into its own dust type, with an exact
original-head/anchor density correction, gives a one-sided local maximum, which
forces the head multiplier below the least full-repeat penalty and, above one
half, the two-copy penalty bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Completing a positive head mass into its own dust type, with an exact
old-head/anchor density correction, gives an actual one-sided local maximum. -/
theorem completion_local_max {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) :
    ∃ η : ℝ, 0 < η ∧ ∀ z r : ℝ, 0 < z → z < η → |r| < η →
      2 * (1 - x.2 i) * r - 2 * x.2 i * z + 2 * r ^ 2 + 2 * r * z + z ^ 2 = 0 →
      -(headRow x.2 (MultipartiteProfiles.dust x) D i -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) * r - head D i * r ^ 2 -
        repeatPenalty D i * x.2 i * z + repeatPenalty D i * r * z + repeatPenalty D i * z ^ 2 / 2 ≤ 0 := by
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
  let η := min (x.2 i / 4) ((1 - b) / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηi : η ≤ x.2 i / 4 := min_le_left _ _
  have hηb : η ≤ (1 - b) / 4 := min_le_right _ _
  refine ⟨η, hη, ?_⟩
  intro z r hz hzη hr hconstraint
  have hr' := abs_lt.mp hr
  have hret : 0 ≤ x.2 i - r - z := by linarith
  have hcorr : 0 ≤ x.2 i - r := by linarith
  have ha : 0 < 1 + r := by linarith
  let p := Function.update x.2 i (x.2 i - r - z)
  have hp' (k : ℕ) : 0 ≤ p k := by
    by_cases hk : k = i
    · subst k
      simpa [p] using hret
    · simpa [p, Function.update_of_ne, hk] using hp k
  have hp1' (k : ℕ) : p k ≤ 1 + r := by
    by_cases hk : k = i
    · subst k
      simp only [p, Function.update_self]
      linarith [hpb i]
    · simp only [p, Function.update_of_ne hk]
      linarith [hpb k]
  have hs := MultipartiteProfiles.dust_nonneg hx.1
  have htotal : 1 + r + (MultipartiteProfiles.dust x + z) + (∑' k, p k) = 1 + x.1 := by
    rw [show p = Function.update x.2 i (x.2 i - r - z) from rfl,
      (hsum.hasSum.update i (x.2 i - r - z)).tsum_eq,
      MultipartiteProfiles.dust_eq_sub_tsum hx.1]
    ring
  have hmoment : (1 + r) ^ 2 + (∑' k, (p k) ^ 2) =
      2 * ε * (1 + r + (MultipartiteProfiles.dust x + z) + ∑' k, p k) ^ 2 := by
    have hpdef : p = Function.update x.2 i (x.2 i + (-r - z)) := by
      dsimp only [p]
      congr 1
      ring
    rw [htotal, hpdef, square_tsum_update x.2 hsqsum i (-r - z)]
    have hold : 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
    nlinarith
  obtain ⟨E, hE, hEobj⟩ := exists_completed_head_objective hD x.2 hp hsum
    (MultipartiteProfiles.dust x) hs i (1 + r) r z hz hret
  have hraw := physicalObjective_le_density_maximum hε hmax hxvalue.le (1 + r) ha
    p hp' hp1' (hsum.update i _) (MultipartiteProfiles.dust x + z) (by positivity) hmoment hE
  rw [htotal] at hraw
  have hden : 0 < (1 + x.1) ^ 2 := by
    have hx0 : 0 ≤ x.1 := hx.1.1.1.1
    positivity
  have hbound := (div_le_div_iff_of_pos_right hden).mp hraw
  have hcorrObj : physicalObjective (1 + r) (Function.update x.2 i (x.2 i - r))
      (MultipartiteProfiles.dust x) D = objective x.2 (MultipartiteProfiles.dust x) D -
        (headRow x.2 (MultipartiteProfiles.dust x) D i -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) * r - head D i * r ^ 2 := by
    rw [physicalObjective_eq_objective,
      objective_update hD x.2 hp hsum (MultipartiteProfiles.dust x) i _ hcorr,
      anchorRow_update hD x.2 hp hsum (MultipartiteProfiles.dust x) i]
    ring
  rw [show p = Function.update x.2 i (x.2 i - r - z) from rfl, hEobj, hcorrObj, hopt] at hbound
  nlinarith

/-- Actual partial completion forces the head multiplier below the least
full-repeat penalty. The correction is an exact quadratic root. -/
theorem multiplier_le_repeatPenalty {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (i : ℕ) (hi : 0 < x.2 i)
    (hrow : headRow x.2 (MultipartiteProfiles.dust x) D i -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 i - 1)) :
    ℓ ≤ repeatPenalty D i := by
  let ci := headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D
  let K := repeatPenalty D i
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  have hiQ := (MultipartiteProfiles.squares_summable hx.1).le_tsum i (fun _ _ => sq_nonneg _)
  have hpi : x.2 i < 1 := by nlinarith
  have hden : 0 < 1 - x.2 i := by linarith
  let κ := x.2 i / (1 - x.2 i)
  have hκ : κ * (1 - x.2 i) = x.2 i := div_mul_cancel₀ _ hden.ne'
  obtain ⟨η, hη, hlocal⟩ := completion_local_max hε hx hmax hxvalue hD hopt i hi
  let η' := η / (|κ| + 2)
  have hη' : 0 < η' := div_pos hη (by positivity)
  have hηeq : η' * (|κ| + 2) = η :=
    div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < |κ| + 2))
  have hηle : η' ≤ η := div_le_self hη.le (by linarith [abs_nonneg κ])
  have hlinear := Variation.tangent_linear_nonpos_of_right_local_max
    (2 * κ ^ 2 + 2 * κ + 1) (2 * (1 - x.2 i)) (2 * κ + 1) 2
    (-ci * κ - K * x.2 i) (-ci) (-head D i * κ ^ 2 + K * κ + K / 2)
    ((-2 * head D i * κ + K) / 2) (-head D i)
    (by linarith) η' hη' (by
      intro t r ht htη hr hroot
      have hrt : |κ * t + r| < η := by
        have htri := abs_add_le (κ * t) r
        rw [abs_mul, abs_of_pos ht] at htri
        have hprod := mul_le_mul_of_nonneg_left htη.le (abs_nonneg κ)
        nlinarith
      have htη' : t < η := htη.trans_le hηle
      have hconstraint : 2 * (1 - x.2 i) * (κ * t + r) - 2 * x.2 i * t +
          2 * (κ * t + r) ^ 2 + 2 * (κ * t + r) * t + t ^ 2 = 0 := by
        have hκt := congrArg (fun z : ℝ => z * t) hκ
        nlinarith [hroot]
      have h := hlocal t (κ * t + r) ht htη' hrt hconstraint
      change -ci * (κ * t + r) - head D i * (κ * t + r) ^ 2 -
        K * x.2 i * t + K * (κ * t + r) * t + K * t ^ 2 / 2 ≤ 0 at h
      convert h using 1
      ring)
  have hlin : -ci * κ = ℓ * x.2 i := by
    have hrow' : ci = ℓ * (x.2 i - 1) := hrow
    have hrowκ := congrArg (fun z : ℝ => z * κ) hrow'
    have hκℓ := congrArg (fun z : ℝ => ℓ * z) hκ
    nlinarith
  rw [hlin] at hlinear
  have hprod : (ℓ - K) * x.2 i ≤ 0 := by nlinarith
  have hnonpos := nonpos_of_mul_nonpos_left hprod hi
  exact sub_nonpos.mp hnonpos

/-- Under the head-count hypothesis above one half, actual completion and
all-count threshold control give the required two-copy penalty bound. -/
theorem twoRepeat_bounds_of_half_lt_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hℓ : 1 / 2 < ℓ) (i : ℕ) (hi : 0 < x.2 i) (hti : head D i < 1)
    (hrow : headRow x.2 (MultipartiteProfiles.dust x) D i -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 i - 1)) :
    ℓ ≤ twoRepeatPenalty D i ∧ repeatPenalty D i = twoRepeatPenalty D i ∧ ℓ < 1 := by
  have hfull := multiplier_le_repeatPenalty hε hx hmax hxvalue hD hopt ℓ i hi hrow
  have heq := repeatPenalty_eq_two_of_half_lt_repeat hD hti (hℓ.trans_le hfull)
  exact ⟨by rwa [← heq], heq, hfull.trans_lt ((repeatPenalty_le_head hD i).trans_lt hti)⟩

end Erdos1017.MultipartiteCountableDual
