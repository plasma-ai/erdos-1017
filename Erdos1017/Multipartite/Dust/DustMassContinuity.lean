module

public import Erdos1017.Multipartite.Dust.DustSingleMerge
public import Mathlib.Tactic.Linarith

/-!
# Lipschitz dependence on dust mass

The objective has an explicit dust-mass modulus uniform over all feasible
coefficients, and the same modulus holds for optimized finite-head values.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteDust

open scoped BigOperators

/-- An explicit dust-mass modulus, uniform over all feasible coefficients. -/
theorem objective_dust_lipschitz {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i)
    (s t T : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hT : (∑ i, p i) + max s t ≤ T)
    {D : Coefficients m} (hD : D ∈ feasible m) :
    |objective p s D - objective p t D| ≤ (1 + T) * |s - t| := by
  have hp₀ : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp i)
  have hc₀ : 0 ≤ ∑ i, incident D i * p i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hD.1.1 _) (hp i))
  have hc₁ : (∑ i, incident D i * p i) ≤ ∑ i, p i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_of_le_one_left (hp i) (hD.1.2 _)
  have hv₀ : 0 ≤ linear D := hD.1.1 _
  have hv₁ : linear D ≤ 1 := hD.1.2 _
  have hq₀ : 0 ≤ penalty D := hD.1.1 _
  have hq₁ : penalty D ≤ 1 := hD.1.2 _
  have hq : penalty D * ((s + t) / 2) ≤ (s + t) / 2 :=
    mul_le_of_le_one_left (by positivity) hq₁
  have hT₀ : 0 ≤ T := by linarith [le_max_left s t]
  have havg : (s + t) / 2 ≤ max s t := by
    linarith [le_max_left s t, le_max_right s t]
  have hbound : |linear D - (∑ i, incident D i * p i) - penalty D * ((s + t) / 2)| ≤
      1 + T := by
    rw [abs_le]
    constructor
    · linarith
    · have hn : 0 ≤ penalty D * ((s + t) / 2) := mul_nonneg hq₀ (by positivity)
      linarith
  have heq : objective p s D - objective p t D =
      (linear D - (∑ i, incident D i * p i) - penalty D * ((s + t) / 2)) * (s - t) := by
    simp only [objective, ← Finset.sum_mul]
    ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

/-- The same modulus holds for actual optimized finite-head values. -/
theorem value_dust_lipschitz {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i)
    (s t T : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hT : (∑ i, p i) + max s t ≤ T) :
    |value p s - value p t| ≤ (1 + T) * |s - t| := by
  obtain ⟨D, hD, hDs⟩ := exists_value_eq p s
  obtain ⟨E, hE, hEt⟩ := exists_value_eq p t
  have h₁ := (abs_le.mp (objective_dust_lipschitz p hp s t T hs ht hT hD)).2
  have h₂ := (abs_le.mp (objective_dust_lipschitz p hp s t T hs ht hT hE)).1
  have hDt := objective_le_value p t D hD
  have hEs := objective_le_value p s E hE
  rw [abs_le]
  constructor <;> linarith

end Erdos1017.MultipartiteDust
