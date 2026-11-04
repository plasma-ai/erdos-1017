module

public import Erdos1017.IntegerTransfer.ThinningBaseSelection

/-!
# Normalized thinning budget and size threshold

The base sampling budget is normalized after fixing order, exception and
squared-error thresholds at retained-edge scales, and a single part-size
threshold absorbs every inverse allocation factor.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

/-- The exact score budget after choosing order, exception and squared-error
thresholds at their natural retained-edge scales. -/
theorem baseSamplingBudget_normalized (n u m : ℕ) (hn : 0 < n) (hu : 0 < u)
    (α δ η L ζ θ : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hη : 0 < η) (hL : 0 < L) (hθ : 0 < θ) :
    L * baseSamplingBudget n u α δ ζ (θ * α * (n : ℝ) ^ 2)
      (η * α * (n : ℝ) ^ 2 / (16 * L))
      (η ^ 3 * α * (n : ℝ) ^ 2 * (degreeScale n u m α) ^ 2 / (128 * L)) =
      L / (θ ^ 2 * α ^ 2 * (n : ℝ) ^ 2) + 16 * L ^ 2 * ζ / (η * δ) +
        128 * L ^ 2 * u / (δ * η ^ 3 * (α ^ m) ^ 2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ u = (n : ℝ) ^ (u - 1) * n := by
    rw [← pow_succ]
    congr 1
    omega
  unfold baseSamplingBudget degreeScale
  rw [hpow]
  field_simp

/-- A single part-size threshold absorbs every inverse allocation factor.
The positive regularity and matching parameters are fixed before α₀. -/
theorem exists_thinning_size_threshold (u m : ℕ) (hu : 0 < u)
    (δ η L D₀ α₀ θ : ℝ) (hδ : 0 < δ) (hη : 0 < η) (hL : 0 < L)
    (hD₀ : 0 < D₀) (hα₀ : 0 < α₀) (hθ : 0 < θ) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∀ α : ℝ, α₀ ≤ α →
      D₀ ≤ degreeScale n u m α ∧
      (n : ℝ) ^ (u - 1) ≤ η * degreeScale n u m α ∧
      L * baseSamplingBudget n u α δ (η * δ / (128 * L ^ 2))
        (θ * α * (n : ℝ) ^ 2) (η * α * (n : ℝ) ^ 2 / (16 * L))
        (η ^ 3 * α * (n : ℝ) ^ 2 * (degreeScale n u m α) ^ 2 / (128 * L)) < 1 := by
  let a₀ := α₀ ^ m
  have ha₀ : 0 < a₀ := pow_pos hα₀ _
  let C₁ := 8 * L / (θ ^ 2 * α₀ ^ 2)
  let C₂ := 1024 * L ^ 2 * u / (δ * η ^ 3 * a₀ ^ 2)
  let C₃ := D₀ / a₀
  let C₄ := 1 / (η * a₀)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; positivity
  have hC₄ : 0 ≤ C₄ := by dsimp [C₄]; positivity
  let R := 1 + C₁ + C₂ + C₃ + C₄
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt R
  have hn₀pos : 0 < n₀ := by
    have h : (0 : ℝ) < n₀ := by dsimp only [R] at hn₀; linarith
    exact_mod_cast h
  refine ⟨n₀, hn₀pos, ?_⟩
  intro n hn α hα
  have hnR : R < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
  have hn1 : 1 < (n : ℝ) := by dsimp only [R] at hnR; linarith
  have hn' : (0 : ℝ) < n := by linarith
  have hnpos : 0 < n := by exact_mod_cast hn'
  have hnC₁ : C₁ < (n : ℝ) := by dsimp only [R] at hnR; linarith
  have hnC₂ : C₂ < (n : ℝ) := by dsimp only [R] at hnR; linarith
  have hnC₃ : C₃ < (n : ℝ) := by dsimp only [R] at hnR; linarith
  have hnC₄ : C₄ < (n : ℝ) := by dsimp only [R] at hnR; linarith
  have hαpos := hα₀.trans_le hα
  have hαm : a₀ ≤ α ^ m := pow_le_pow_left₀ hα₀.le hα m
  have hαmpos : 0 < α ^ m := pow_pos hαpos _
  have hpow : (n : ℝ) ^ u = (n : ℝ) ^ (u - 1) * n := by
    rw [← pow_succ]
    congr 1
    omega
  have hnpred : 1 ≤ (n : ℝ) ^ (u - 1) := one_le_pow₀ hn1.le
  have hnpow : (n : ℝ) ≤ (n : ℝ) ^ u := by rw [hpow]; nlinarith
  have hdegree : D₀ ≤ degreeScale n u m α := by
    have hscale : D₀ < (n : ℝ) * a₀ := (div_lt_iff₀ ha₀).mp hnC₃
    have hprod := mul_le_mul hnpow hαm ha₀.le (pow_nonneg hn'.le u)
    dsimp only [degreeScale]
    exact hscale.le.trans hprod
  have hcodegree : (n : ℝ) ^ (u - 1) ≤ η * degreeScale n u m α := by
    have hscale : 1 < (n : ℝ) * (η * a₀) := (div_lt_iff₀ (mul_pos hη ha₀)).mp hnC₄
    have hmono := mul_le_mul_of_nonneg_left hαm (mul_nonneg hη.le hn'.le)
    have hlow : 1 ≤ η * n * α ^ m := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlow (pow_nonneg hn'.le (u - 1))
    dsimp only [degreeScale]
    rw [hpow]
    nlinarith
  have hterm₁ : L / (θ ^ 2 * α ^ 2 * (n : ℝ) ^ 2) < 1 / 8 := by
    have hscale : 8 * L < (n : ℝ) * (θ ^ 2 * α₀ ^ 2) :=
      (div_lt_iff₀ (by positivity : 0 < θ ^ 2 * α₀ ^ 2)).mp hnC₁
    have hsq : α₀ ^ 2 ≤ α ^ 2 := by nlinarith
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hprod := mul_le_mul hsq hn2 hn'.le (sq_nonneg α)
    have hprod' := mul_le_mul_of_nonneg_left hprod (sq_nonneg θ)
    apply (div_lt_iff₀ (by positivity : 0 < θ ^ 2 * α ^ 2 * (n : ℝ) ^ 2)).mpr
    nlinarith only [hscale, hprod']
  have hterm₂ : 16 * L ^ 2 * (η * δ / (128 * L ^ 2)) / (η * δ) = 1 / 8 := by
    field_simp
    all_goals ring
  have hterm₃ : 128 * L ^ 2 * u / (δ * η ^ 3 * (α ^ m) ^ 2 * n) < 1 / 8 := by
    have hscale : 1024 * L ^ 2 * u < (n : ℝ) * (δ * η ^ 3 * a₀ ^ 2) :=
      (div_lt_iff₀ (by positivity : 0 < δ * η ^ 3 * a₀ ^ 2)).mp hnC₂
    have hsq : a₀ ^ 2 ≤ (α ^ m) ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (n : ℝ) * δ * η ^ 3)
    apply (div_lt_iff₀ (by positivity : 0 < δ * η ^ 3 * (α ^ m) ^ 2 * n)).mpr
    nlinarith only [hscale, hprod]
  refine ⟨hdegree, hcodegree, ?_⟩
  rw [baseSamplingBudget_normalized n u m hnpos hu α δ η L _ θ hαpos hδ hη hL hθ, hterm₂]
  linarith

end Erdos1017.TransversalThinning
