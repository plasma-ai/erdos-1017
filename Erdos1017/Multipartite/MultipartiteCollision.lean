module

public import Erdos1017.Multipartite.ClosedAnchoring
public import Erdos1017.Multipartite.Selector.SelectorCollision
public import Erdos1017.Multipartite.DenseMultipartite

/-!
# Finite collision estimate for multipartite values

Homogeneous normalization identifies the collision curve with the split curve,
giving the normalized finite collision estimate for a largest-part mass vector
and the finite multipartite upper bound on the dense interval.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Multipartite

open scoped BigOperators

/-- Homogeneous normalization identifies the collision curve with the split curve. -/
theorem collision_curve_normalization {a : ℝ} (ha : 0 < a) :
    a ^ 2 * Selector.Collision.collisionCurve ((1 - a) / a) = Benchmark.splitValue a := by
  by_cases h : a = 1
  · subst a
    norm_num [Selector.Collision.collisionCurve, Benchmark.splitValue, Benchmark.splitIndex]
  have hT : (1 - a) / a ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm h)) ha.ne'
  have hj : (0 : ℝ) < Benchmark.splitIndex a := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))
  simp only [Selector.Collision.collisionCurve, hT, ↓reduceIte, Selector.Collision.drawIndex,
    Benchmark.splitValue, ha.ne', Benchmark.splitIndex]
  field_simp
  ring

/-- The normalized finite collision estimate for a largest-part mass vector. -/
theorem value_le_split_add_collision {m : ℕ} (a : Option (Fin m) → ℝ)
    (ha : 0 < a none) (hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none)
    (hsum : ∑ i, a i = 1) :
    value a ≤ Benchmark.splitValue (a none) + (∑ i, a (some i) ^ 2) / 2 := by
  let p : Fin m → ℝ := fun i => a (some i) / a none
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i
    exact ⟨div_nonneg (hsecondary i).1 ha.le, (div_le_one ha).mpr (hsecondary i).2⟩
  have hT : ∑ i, p i = (1 - a none) / a none := by
    dsimp [p]
    rw [← Finset.sum_div]
    congr 1
    simp only [Fintype.sum_option] at hsum
    linarith
  have hQ : a none ^ 2 * ∑ i, p i ^ 2 = ∑ i, a (some i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p]
    field_simp
  have hbound := (Selector.Collision.value_le_collision_bound p hp).trans (min_le_right _ _)
  rw [largest_part_anchoring a ha hsecondary]
  calc
    a none ^ 2 * Selector.value p ≤ a none ^ 2 *
        (Selector.Collision.collisionCurve (∑ i, p i) + (∑ i, p i ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg (a none))
    _ = Benchmark.splitValue (a none) + (∑ i, a (some i) ^ 2) / 2 := by
      rw [mul_add, hT, collision_curve_normalization ha, ← mul_div_assoc, hQ]

/-- The finite multipartite upper bound on the dense interval. -/
theorem dense_value_le_benchmark {m : ℕ} (a : Option (Fin m) → ℝ)
    (ha : 0 < a none) (hsecondary : ∀ i, 0 ≤ a (some i) ∧ a (some i) ≤ a none)
    (hsum : ∑ i, a i = 1) (hsquares : ∑ i, a i ^ 2 ≤ (4 / 13 : ℝ) ^ 2) :
    value a ≤ benchmark ((1 - ∑ i, a i ^ 2) / 2) := by
  let r : ℝ := Real.sqrt (∑ i, a i ^ 2)
  have hsum_nonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  have hr_sq : r ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt hsum_nonneg
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hq : r ^ 2 = a none ^ 2 + ∑ i, a (some i) ^ 2 := by
    rw [hr_sq, Fintype.sum_option]
  have har : a none ≤ r := by
    have htail : 0 ≤ ∑ i, a (some i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (a (some i)))
    nlinarith
  have hr : r ≤ 4 / 13 := by nlinarith
  have h := DenseMultipartite.collision_bound_le_benchmark ha har hr hq
    (value_le_split_add_collision a ha hsecondary hsum)
  simpa only [hr_sq] using h

end Erdos1017.Multipartite
