module

public import Erdos1017.Multipartite.MultipartitePartVariation

/-!
# Dust-mass variations of the countable objective

`dustRow` is the homogeneous dust row with its internal negative charge;
changing dust mass has exactly the quadratic charge of the dust type, and
balanced head and dust transfers give the physical quadratic variation including
the dust diagonal.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- The homogeneous dust row, with its actual internal negative charge. -/
def dustRow (p : ℕ → ℝ) (s : ℝ) (D : Coefficients) : ℝ :=
  linear D - (∑' i, incident D i * p i) - penalty D * s

/-- Changing dust mass has exactly the quadratic charge of the existing
homogeneous dust type. -/
theorem objective_dust_update (p : ℕ → ℝ) (s y : ℝ) (D : Coefficients) :
    objective p y D = objective p s D + (y - s) * dustRow p s D - penalty D * (y - s) ^ 2 / 2 := by
  unfold objective dustRow
  simp only [tsum_mul_right]
  ring

theorem dustRow_head_update {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ) (i : ℕ) (y : ℝ) :
    dustRow (Function.update p i y) s D = dustRow p s D - incident D i * (y - p i) := by
  have heq : (fun k => incident D k * Function.update p i y k) =
      Function.update (fun k => incident D k * p k) i (incident D i * y) := by
    funext k
    by_cases hk : k = i <;> simp [Function.update_of_ne, hk]
  have h := ((incident_summable p hp hsum hD.1).hasSum.update i (incident D i * y)).tsum_eq
  unfold dustRow
  rw [heq, h]
  ring

theorem anchorRow_dust_update (p : ℕ → ℝ) (s y : ℝ) (D : Coefficients) :
    anchorRow p y D = anchorRow p s D + linear D * (y - s) := by
  unfold anchorRow
  ring

/-- Moving one head mass and dust mass, balanced at the anchor, gives the
actual physical quadratic variation including the dust diagonal. -/
theorem physicalObjective_head_dust_transfers {D : Coefficients} (hD : D ∈ feasible)
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) (s : ℝ)
    (i : ℕ) (t r : ℝ) (ht : 0 ≤ p i + t) :
    physicalObjective (1 - t - r) (Function.update p i (p i + t)) (s + r) D =
      objective p s D + t * (headRow p s D i - anchorRow p s D) +
        r * (dustRow p s D - anchorRow p s D) - head D i * t ^ 2 -
        (linear D + penalty D / 2) * r ^ 2 -
        (incident D i + head D i + linear D) * t * r := by
  rw [physicalObjective_eq_objective,
    objective_dust_update _ s (s + r), dustRow_head_update hD p hp hsum s i,
    objective_update hD p hp hsum s i _ ht, anchorRow_dust_update _ s (s + r),
    anchorRow_update hD p hp hsum s i]
  ring

/-- A single head replacement changes the square moment by its explicit
linear and quadratic increments. -/
theorem square_tsum_update (p : ℕ → ℝ) (hsum : Summable (fun k => (p k) ^ 2)) (i : ℕ) (t : ℝ) :
    (∑' k, (Function.update p i (p i + t) k) ^ 2) =
      (∑' k, (p k) ^ 2) + 2 * p i * t + t ^ 2 := by
  have heq : (fun k => (Function.update p i (p i + t) k) ^ 2) =
      Function.update (fun k => (p k) ^ 2) i ((p i + t) ^ 2) := by
    funext k
    by_cases hk : k = i <;> simp [Function.update_of_ne, hk]
  rw [heq, (hsum.hasSum.update i ((p i + t) ^ 2)).tsum_eq]
  ring

end Erdos1017.MultipartiteCountableDual
