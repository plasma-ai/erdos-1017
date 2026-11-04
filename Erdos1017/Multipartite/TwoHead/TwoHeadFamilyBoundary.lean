module

public import Erdos1017.Multipartite.TwoHead.TwoHeadCountLaw
public import Erdos1017.Multipartite.MultipartiteCollision
public import Erdos1017.Multipartite.OneHeadLowDensityScalar

/-!
# Boundary values and split comparators of the two-head family

The short-profile count law and split bounds are independent of the benchmark's
branch comparison and the selected-model arguments.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.TwoHeadFamilyBoundary

theorem value_zero_head {S : ℝ} (hS : 0 ≤ S) :
    MultipartiteDust.value (fun _ : Fin 1 => (0 : ℝ)) S =
      Selector.Collision.collisionCurve S := by
  by_cases hS0 : S = 0
  · subst S
    rw [TwoHeadCountLaw.value_zero_dust (by norm_num)]
    simp [Selector.Collision.collisionCurve]
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  have hindex : TwoHeadCountLaw.selectedIndex 0 S = ⌈S⌉₊ := by
    unfold TwoHeadCountLaw.selectedIndex
    have hR : TwoHeadCountLaw.conditionalMoment 0 S ⌊S⌋₊ / S = S := by
      simp [TwoHeadCountLaw.conditionalMoment, pow_two, hS0]
    rw [hR]
  have hdraw : Selector.Collision.drawIndex S = ⌈S⌉₊ :=
    max_eq_right (Nat.one_le_ceil_iff.mpr hSpos)
  rw [TwoHeadCountLaw.value_eq_selected (by norm_num) (by norm_num) hSpos]
  simp only [hindex, Selector.Collision.collisionCurve, hS0, ite_false, hdraw,
    TwoHeadCountLaw.cellValue, zero_mul, mul_zero, sub_zero, zero_add]
  ring

theorem zero_head_scaled {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    r ^ 2 * MultipartiteDust.value (fun _ : Fin 1 => (0 : ℝ)) ((1 - r) / r) =
      Benchmark.splitValue r := by
  rw [value_zero_head (div_nonneg (by linarith) hr.le)]
  exact Multipartite.collision_curve_normalization hr

/-- The actual one-independent-head boundary has exactly the split value. -/
theorem zero_head_normalization {S : ℝ} (hS : 0 ≤ S) :
    MultipartiteDust.value (fun _ : Fin 1 => (0 : ℝ)) S / (1 + S) ^ 2 =
      Benchmark.splitValue (1 / (1 + S)) := by
  have hd : 0 < 1 + S := by linarith
  have hr : 0 < 1 / (1 + S) := by positivity
  have hr1 : 1 / (1 + S) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hS' : (1 - 1 / (1 + S)) / (1 / (1 + S)) = S := by
    field_simp
    ring
  have h := zero_head_scaled hr hr1
  rw [hS'] at h
  convert h using 1
  field_simp

/-- Every fixed-index split polynomial is a feasible lower comparator for
the actual split envelope, throughout the closed physical radius range. -/
theorem splitPolynomial_le_splitValue (j : ℕ) (hj : 0 < j) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : Benchmark.splitPolynomial j r ≤ Benchmark.splitValue r := by
  have hj0 : (j : ℝ) ≠ 0 := (Nat.cast_pos.mpr hj).ne'
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  by_cases hr0 : r = 0
  · subst r
    simp only [Benchmark.splitPolynomial, Benchmark.splitValue, ite_true,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have h := mul_le_mul_of_nonneg_left
    (TwoHeadCountLaw.cellValue_le_value j 0 hj (Nat.zero_le _) 0 ((1 - r) / r)) (sq_nonneg r)
  rw [zero_head_scaled hrpos hr.2] at h
  have hid : r ^ 2 * TwoHeadCountLaw.cellValue j 0 0 ((1 - r) / r) =
      Benchmark.splitPolynomial j r := by
    unfold TwoHeadCountLaw.cellValue Benchmark.splitPolynomial
    norm_num
    field_simp
    ring
  rwa [hid] at h

/-- The actual one-head lower test gives the dimension-free split floor. -/
theorem splitValue_lower_bound {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    r ^ 2 * (1 - r) ≤ Benchmark.splitValue r := by
  by_cases hr0 : r = 0
  · subst r
    simp [Benchmark.splitValue]
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  let S := (1 - r) / r
  have hS : 0 ≤ S := div_nonneg (by linarith [hr.2]) hr.1
  have hd : 0 < 1 + S := by linarith
  have h := MultipartiteProfiles.oneHeadValue_lower_bound (x := 0) (S := S)
    (by norm_num) hS
  rw [MultipartiteProfiles.oneHeadValue_eq_finite] at h
  have hactual : S / (1 + S) ≤ MultipartiteDust.value (fun _ : Fin 1 => (0 : ℝ)) S := by
    simpa using h
  have hscaled := mul_le_mul_of_nonneg_left hactual (sq_nonneg r)
  rw [show S = (1 - r) / r from rfl, zero_head_scaled hrpos hr.2] at hscaled
  have hid : r ^ 2 * (((1 - r) / r) / (1 + (1 - r) / r)) = r ^ 2 * (1 - r) := by
    have hd' : 1 + (1 - r) / r ≠ 0 := ne_of_gt hd
    field_simp
    ring
  rwa [hid] at hscaled

/-- Four actual nonempty count types give the singleton-pair bound when
the total secondary mass is at most one. -/
theorem value_le_short {x S : ℝ} (hx : 0 ≤ x) (hS : 0 ≤ S) (hT : x + S ≤ 1) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S ≤ x + S - x * S - S ^ 2 / 2 := by
  let w : Fin 4 → ℝ := ![x * S, S ^ 2 / 2, x * (1 - S), S * (1 - x - S)]
  let b : Fin 4 → Bool := ![true, false, true, false]
  let k : Fin 4 → ℕ := ![1, 2, 0, 1]
  have hw (ω : Fin 4) : 0 ≤ w ω := by
    fin_cases ω
    · change 0 ≤ x * S
      positivity
    · change 0 ≤ S ^ 2 / 2
      positivity
    · change 0 ≤ x * (1 - S)
      exact mul_nonneg hx (by linarith)
    · change 0 ≤ S * (1 - x - S)
      exact mul_nonneg hS (by linarith)
  have hm :
      (∑ ω, w ω * Selector.bit (b ω)) = x ∧
        (∑ ω, w ω * (k ω : ℝ)) = S ∧
        (∑ ω, w ω * Selector.bit (b ω) * (k ω : ℝ)) = x * S ∧
        (∑ ω, w ω * (k ω : ℝ) * ((k ω : ℝ) - 1)) = S ^ 2 := by
    norm_num [Fin.sum_univ_succ, w, b, k, Selector.bit]
    constructor <;> ring
  have hsum : (∑ ω, w ω) = x + S - x * S - S ^ 2 / 2 := by
    norm_num [Fin.sum_univ_succ, w]
    ring
  have h := TwoHeadCountLaw.value_le_count_law w b k hw x S
    hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  rwa [hsum] at h

theorem normalized_value_le_missing {x S : ℝ} (hx : 0 ≤ x) (hS : 0 ≤ S)
    (hT : x + S ≤ 1) :
    MultipartiteDust.value (fun _ : Fin 1 => x) S / (1 + x + S) ^ 2 ≤
      (1 + x ^ 2) / (2 * (1 + x + S) ^ 2) := by
  have hd : 0 < (1 + x + S) ^ 2 := by positivity
  rw [div_mul_eq_div_div]
  apply (div_le_div_iff_of_pos_right hd).mpr
  have h := value_le_short hx hS hT
  nlinarith [sq_nonneg (1 - x - S)]

theorem normalized_unit_head_le_missing {S : ℝ} (hS : 0 ≤ S) :
    MultipartiteDust.value (fun _ : Fin 1 => (1 : ℝ)) S / (2 + S) ^ 2 ≤
      (1 + (1 : ℝ) ^ 2) / (2 * (2 + S) ^ 2) := by
  rw [TwoHeadCountLaw.value_unit_head hS]
  norm_num [div_mul_eq_div_div]

end Erdos1017.TwoHeadFamilyBoundary
