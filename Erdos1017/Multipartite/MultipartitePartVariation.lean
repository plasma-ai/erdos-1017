module

public import Erdos1017.Multipartite.Countable.CountableMassSwap
public import Erdos1017.Models.Selection.QuadraticConstraint

/-!
# Two-head transfers and the row multiplier

Two-head mass transfers remain admissible near a selected density maximum, exact
density preservation forces the dual's quadratic gain to be nonpositive, and the
regular part-mass constraint determines a common row slope, so every selected
optimizer with a positive secondary head has its own unique row multiplier.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- Actual two-head mass transfers remain admissible near a selected density
maximum. Exact density preservation forces the old dual's quadratic gain to
be nonpositive; no variational conclusion is assumed. -/
theorem two_transfer_local_max {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    ∃ η : ℝ, 0 < η ∧ ∀ t r : ℝ, |t| < η → |r| < η →
      2 * (x.2 i - 1) * t + 2 * (x.2 j - 1) * r + 2 * t ^ 2 + 2 * t * r + 2 * r ^ 2 = 0 →
      t * (headRow x.2 (MultipartiteProfiles.dust x) D i -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) +
        r * (headRow x.2 (MultipartiteProfiles.dust x) D j -
          anchorRow x.2 (MultipartiteProfiles.dust x) D) - head D i * t ^ 2 - head D j * r ^ 2 +
        (MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) -
          head D i - head D j) * t * r ≤ 0 := by
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
  let η := min (x.2 i / 2) (min (x.2 j / 2) ((1 - b) / 4))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hηi : η ≤ x.2 i / 2 := min_le_left _ _
  have hηj : η ≤ x.2 j / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η ≤ (1 - b) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, ?_⟩
  intro t r ht hr hconstraint
  have ht' := abs_lt.mp ht
  have hr' := abs_lt.mp hr
  have hti : 0 ≤ x.2 i + t := by linarith
  have hrj : 0 ≤ x.2 j + r := by linarith
  have ha : 0 < 1 - t - r := by linarith
  let p := replaceTwo x.2 i j (x.2 i + t) (x.2 j + r)
  have hp' : ∀ k, 0 ≤ p k := replaceTwo_nonneg x.2 hp i j _ _ hti hrj
  have hp1' (k : ℕ) : p k ≤ 1 - t - r := by
    by_cases hkj : k = j
    · subst k
      simp only [p, replaceTwo, Function.update_self]
      linarith [hpb j]
    · by_cases hki : k = i
      · subst k
        simp only [p, replaceTwo, Function.update_of_ne hij, Function.update_self]
        linarith [hpb i]
      · simp only [p, replaceTwo, Function.update_of_ne hkj, Function.update_of_ne hki]
        linarith [hpb k]
  have hs := MultipartiteProfiles.dust_nonneg hx.1
  have htotal : 1 - t - r + MultipartiteProfiles.dust x + (∑' k, p k) = 1 + x.1 := by
    rw [show p = replaceTwo x.2 i j (x.2 i + t) (x.2 j + r) from rfl,
      replaceTwo_tsum _ hsum i j hij, MultipartiteProfiles.dust_eq_sub_tsum hx.1]
    ring
  have hmoment : (1 - t - r) ^ 2 + (∑' k, (p k) ^ 2) =
      2 * ε * (1 - t - r + MultipartiteProfiles.dust x + ∑' k, p k) ^ 2 := by
    rw [htotal, show p = replaceTwo x.2 i j (x.2 i + t) (x.2 j + r) from rfl,
      replaceTwo_square_tsum _ hsqsum i j hij]
    have hold : 1 + (∑' k, (x.2 k) ^ 2) = 2 * ε * (1 + x.1) ^ 2 := hx.2
    nlinarith
  have hraw := physicalObjective_le_density_maximum hε hmax hxvalue.le (1 - t - r) ha
    p hp' hp1' ((hsum.update i _).update j _) (MultipartiteProfiles.dust x) hs hmoment hD
  rw [htotal] at hraw
  have hden : 0 < (1 + x.1) ^ 2 := by
    have hx0 : 0 ≤ x.1 := hx.1.1.1.1
    positivity
  have hbound := (div_le_div_iff_of_pos_right hden).mp hraw
  rw [show p = replaceTwo x.2 i j (x.2 i + t) (x.2 j + r) from rfl,
    physicalObjective_two_transfers hD x.2 hp hsum (MultipartiteProfiles.dust x) i j hij t r hti hrj,
    hopt] at hbound
  linarith

/-- The actual regular part-mass constraint determines a common row slope.
For equal positive head masses its tangent second variation also bounds the
pair penalty by that slope. -/
theorem pair_transfer_conditions {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i j : ℕ) (hij : i ≠ j) (hi : 0 < x.2 i) (hj : 0 < x.2 j) :
    (headRow x.2 (MultipartiteProfiles.dust x) D j - anchorRow x.2 (MultipartiteProfiles.dust x) D) *
        (x.2 i - 1) =
      (headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D) *
        (x.2 j - 1) ∧
      (x.2 i = x.2 j →
        -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) ≤
          (headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D) /
            (x.2 i - 1)) := by
  let ci := headRow x.2 (MultipartiteProfiles.dust x) D i - anchorRow x.2 (MultipartiteProfiles.dust x) D
  let cj := headRow x.2 (MultipartiteProfiles.dust x) D j - anchorRow x.2 (MultipartiteProfiles.dust x) D
  let b := MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j))
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  have hsqsum := MultipartiteProfiles.squares_summable hx.1
  have hpi : x.2 i < 1 := by
    have hiQ := hsqsum.le_tsum i (fun _ _ => sq_nonneg _)
    nlinarith
  have hpi0 : x.2 i - 1 ≠ 0 := by linarith
  let ρ := (x.2 j - 1) / (x.2 i - 1)
  have hρ : ρ * (x.2 i - 1) = x.2 j - 1 := div_mul_cancel₀ _ hpi0
  obtain ⟨η, hη, hlocal⟩ := two_transfer_local_max hε hx hmax hxvalue hD hopt i j hij hi hj
  let η' := η / (|ρ| + 2)
  have hη' : 0 < η' := div_pos hη (by positivity)
  have hηeq : η' * (|ρ| + 2) = η :=
    div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < |ρ| + 2))
  have hηle : η' ≤ η := (div_le_self hη.le (by linarith [abs_nonneg ρ] : (1 : ℝ) ≤ |ρ| + 2))
  have hconditions := Variation.lagrange_tangent_conditions_of_local_max
    (2 * (ρ ^ 2 - ρ + 1)) (2 * (1 - x.2 i)) (2 * ρ - 1) 2
    (cj - ρ * ci) (-ci)
    (-head D i * ρ ^ 2 - head D j - ρ * (b - head D i - head D j))
    ((-2 * ρ * head D i - (b - head D i - head D j)) / 2) (-head D i)
    (by linarith) η' hη' (by
      intro t r ht hr hroot
      have hut : |-(ρ * t) - r| < η := by
        have htri := abs_sub (-(ρ * t)) r
        rw [abs_neg, abs_mul] at htri
        have hprod := mul_le_mul_of_nonneg_left ht.le (abs_nonneg ρ)
        nlinarith
      have hvt : |t| < η := ht.trans_le hηle
      have hconstraint : 2 * (x.2 i - 1) * (-(ρ * t) - r) +
          2 * (x.2 j - 1) * t + 2 * (-(ρ * t) - r) ^ 2 +
          2 * (-(ρ * t) - r) * t + 2 * t ^ 2 = 0 := by
        have hρt := congrArg (fun z : ℝ => z * t) hρ
        nlinarith [hroot]
      have h := hlocal (-(ρ * t) - r) t hut hvt hconstraint
      change (-(ρ * t) - r) * ci + t * cj - head D i * (-(ρ * t) - r) ^ 2 -
        head D j * t ^ 2 + (b - head D i - head D j) * (-(ρ * t) - r) * t ≤ 0 at h
      convert h using 1
      ring)
  constructor
  · change cj * (x.2 i - 1) = ci * (x.2 j - 1)
    have h := hconditions.1
    dsimp [ρ] at h
    field_simp [hpi0] at h
    nlinarith
  · intro hijmass
    have hρ1 : ρ = 1 := by
      dsimp [ρ]
      rw [← hijmass]
      exact div_self hpi0
    have h := hconditions.2
    rw [hρ1] at h
    have hfrac : (-ci) * (2 * ((1 : ℝ) ^ 2 - 1 + 1)) / (2 * (1 - x.2 i)) =
        ci / (x.2 i - 1) := by
      have hden : 1 - x.2 i ≠ 0 := by linarith
      field_simp [hpi0, hden]
      ring
    rw [hfrac] at h
    change -b ≤ ci / (x.2 i - 1)
    nlinarith

/-- Every selected optimizer with a positive secondary head has its own
unique row multiplier, derived from actual mass transfers. Every positive
head pair obeys the corresponding multiplier bound. -/
theorem exists_unique_head_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (i : ℕ) (hi : 0 < x.2 i) :
    ∃ ℓ : ℝ,
      (∀ j, 0 < x.2 j → headRow x.2 (MultipartiteProfiles.dust x) D j -
          anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 j - 1)) ∧
      (∀ j k, j ≠ k → 0 < x.2 j → 0 < x.2 k →
        -MultipartiteCountableMeasure.kernel D (.inl (some j)) (.inl (some k)) ≤ ℓ) ∧
      ∀ m : ℝ, (∀ j, 0 < x.2 j → headRow x.2 (MultipartiteProfiles.dust x) D j -
          anchorRow x.2 (MultipartiteProfiles.dust x) D = m * (x.2 j - 1)) → m = ℓ := by
  have hQ := (MultipartiteProfiles.above_missing_density_bounds hx hε hxvalue).1
  have hsqsum := MultipartiteProfiles.squares_summable hx.1
  have hhead (j : ℕ) : x.2 j < 1 := by
    have hjQ := hsqsum.le_tsum j (fun _ _ => sq_nonneg _)
    nlinarith
  have hi0 : x.2 i - 1 ≠ 0 := by linarith [hhead i]
  let ℓ := (headRow x.2 (MultipartiteProfiles.dust x) D i -
    anchorRow x.2 (MultipartiteProfiles.dust x) D) / (x.2 i - 1)
  have hrows (j : ℕ) (hj : 0 < x.2 j) : headRow x.2 (MultipartiteProfiles.dust x) D j -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 j - 1) := by
    by_cases hij : i = j
    · subst j
      dsimp [ℓ]
      rw [div_mul_cancel₀ _ hi0]
    · have h := (pair_transfer_conditions hε hx hmax hxvalue hD hopt i j hij hi hj).1
      dsimp [ℓ]
      field_simp [hi0]
      nlinarith [h]
  refine ⟨ℓ, hrows, ?_, ?_⟩
  · intro j k hjk hj hk
    by_cases heq : x.2 j = x.2 k
    · have h := (pair_transfer_conditions hε hx hmax hxvalue hD hopt j k hjk hj hk).2 heq
      rw [hrows j hj] at h
      have hj0 : x.2 j - 1 ≠ 0 := by linarith [hhead j]
      simpa only [mul_div_cancel_right₀ _ hj0] using h
    · exact pair_le_multiplier_of_ne_mass hx.1 hD hopt ℓ hrows j k hjk hj hk heq
  · intro m hm
    have h := hm i hi
    have h' := hrows i hi
    exact mul_right_cancel₀ hi0 (h.symm.trans h')

end Erdos1017.MultipartiteCountableDual
