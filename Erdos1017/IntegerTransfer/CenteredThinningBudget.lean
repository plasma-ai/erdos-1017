module

public import Erdos1017.IntegerTransfer.CenteredThinningScore
public import Erdos1017.IntegerTransfer.NormalizedThinningMean

/-!
# Decay of the centered sampling budget

After centering the selected exception count, the whole role budget vanishes as
`n` grows, with a uniform `O(1/n)` coefficient and no fixed failure term per
clique type; the decay is uniform for every `α` above a fixed positive floor
(`centeredSamplingBudget_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

/-- After centering the selected exception count, the entire role budget
vanishes as n grows. There is no fixed failure term for each clique type. -/
theorem centeredSamplingBudget_normalized (n u m : ℕ) (hn : 0 < n) (hu : 0 < u)
    (α δ η L θ : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hη : 0 < η) (hL : 0 < L) (hθ : 0 < θ) :
    L * centeredSamplingBudget n u α δ (θ * α * (n : ℝ) ^ 2)
      (η * α * (n : ℝ) ^ 2 / (32 * L))
      (η ^ 3 * α * (n : ℝ) ^ 2 * (degreeScale n u m α) ^ 2 / (128 * L)) =
      L / (θ ^ 2 * α ^ 2 * (n : ℝ) ^ 2) + 1024 * L ^ 3 / (η ^ 2 * α ^ 2 * (n : ℝ) ^ 2) +
        128 * L ^ 2 * u / (δ * η ^ 3 * (α ^ m) ^ 2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ u = (n : ℝ) ^ (u - 1) * n := by
    rw [← pow_succ]
    congr 1
    omega
  unfold centeredSamplingBudget degreeScale
  rw [hpow]
  field_simp
  ring

/-- A uniform O(1/n) coefficient, allowed to depend on the allocation floor. -/
def centeredBudgetCoefficient (u m : ℕ) (δ η L θ α₀ : ℝ) : ℝ :=
  L / (θ ^ 2 * α₀ ^ 2) + 1024 * L ^ 3 / (η ^ 2 * α₀ ^ 2) +
    128 * L ^ 2 * u / (δ * η ^ 3 * (α₀ ^ m) ^ 2)

/-- Uniform centered-score decay for every α above a fixed positive floor.
A finite number of allocation types therefore changes only the size threshold. -/
theorem centeredSamplingBudget_le (n u m : ℕ) (hn : 0 < n) (hu : 0 < u)
    (α α₀ δ η L θ : ℝ) (hα₀ : 0 < α₀) (hα : α₀ ≤ α)
    (hδ : 0 < δ) (hη : 0 < η) (hL : 0 < L) (hθ : 0 < θ) :
    L * centeredSamplingBudget n u α δ (θ * α * (n : ℝ) ^ 2)
      (η * α * (n : ℝ) ^ 2 / (32 * L))
      (η ^ 3 * α * (n : ℝ) ^ 2 * (degreeScale n u m α) ^ 2 / (128 * L)) ≤
      centeredBudgetCoefficient u m δ η L θ α₀ / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hαpos := hα₀.trans_le hα
  have hα2 : α₀ ^ 2 ≤ α ^ 2 := by nlinarith only [hα₀, hα]
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  have hprod := mul_le_mul hα2 hn2 hn'.le (sq_nonneg α)
  have hpow := pow_le_pow_left₀ hα₀.le hα m
  have hpowsq : (α₀ ^ m) ^ 2 ≤ (α ^ m) ^ 2 := by
    nlinarith only [hpow, pow_pos hα₀ m, pow_pos hαpos m]
  have h1 : L / (θ ^ 2 * α ^ 2 * (n : ℝ) ^ 2) ≤ L / (θ ^ 2 * α₀ ^ 2 * n) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hden := mul_le_mul_of_nonneg_left hprod (sq_nonneg θ)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hden]) hL.le
  have h2 : 1024 * L ^ 3 / (η ^ 2 * α ^ 2 * (n : ℝ) ^ 2) ≤
      1024 * L ^ 3 / (η ^ 2 * α₀ ^ 2 * n) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hden := mul_le_mul_of_nonneg_left hprod (sq_nonneg η)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hden]) (by positivity)
  have h3 : 128 * L ^ 2 * u / (δ * η ^ 3 * (α ^ m) ^ 2 * n) ≤
      128 * L ^ 2 * u / (δ * η ^ 3 * (α₀ ^ m) ^ 2 * n) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hden := mul_le_mul_of_nonneg_left hpowsq (by positivity : 0 ≤ δ * η ^ 3 * (n : ℝ))
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hden]) (by positivity)
  rw [centeredSamplingBudget_normalized n u m hn hu α δ η L θ hαpos hδ hη hL hθ]
  calc
    _ ≤ L / (θ ^ 2 * α₀ ^ 2 * n) + 1024 * L ^ 3 / (η ^ 2 * α₀ ^ 2 * n) +
        128 * L ^ 2 * u / (δ * η ^ 3 * (α₀ ^ m) ^ 2 * n) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by unfold centeredBudgetCoefficient; simp only [div_mul_eq_div_div, add_div]

end Erdos1017.TransversalThinning
