module

public import Erdos1017.Benchmark.SplitCurve
public import Mathlib.Order.Monotone.Union

/-!
# Split-curve comparison on the dense interval

The split-curve comparison for finite multipartite profiles on the dense interval.
Its application to the multipartite partition value also needs the finite
collision estimate, which is not part of this module.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.DenseMultipartite

open Benchmark Set

/-- Subtracting the collision correction leaves an increasing split curve. -/
def adjustedSplit (r : ℝ) : ℝ := splitValue r - r ^ 2 / 2

theorem polynomial_difference (j : ℕ) (hj : 0 < j) (a r : ℝ) :
    (splitPolynomial j r - r ^ 2 / 2) - (splitPolynomial j a - a ^ 2 / 2) =
      (r - a) * (2 * ((j : ℝ) + 1) -
        (2 * (j : ℝ) + 1 + (j : ℝ) * ((j : ℝ) + 1) / 2) * (r + a)) /
        ((j : ℝ) * ((j : ℝ) + 1)) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  unfold splitPolynomial
  field_simp
  ring

/-- Every branch of index at least four satisfies the required quadratic correction. -/
theorem polynomial_monotone (j : ℕ) (hj : 4 ≤ j) :
    MonotoneOn (fun r => splitPolynomial j r - r ^ 2 / 2)
      (Icc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ))) := by
  intro a ha r hr har
  have hj' : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ : (0 : ℝ) < j := by linarith
  have ha' := (le_div_iff₀ hj₀).mp ha.2
  have hr' := (le_div_iff₀ hj₀).mp hr.2
  let A : ℝ := 2 * (j : ℝ) + 1 + (j : ℝ) * ((j : ℝ) + 1) / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound := mul_nonneg hA (show 0 ≤ 2 - (j : ℝ) * (r + a) by nlinarith)
  have hquad := mul_nonneg (show 0 ≤ (j : ℝ) - 4 by linarith)
    (show 0 ≤ (j : ℝ) + 1 by linarith)
  have hfactor : 0 ≤ 2 * ((j : ℝ) + 1) - A * (r + a) := by
    dsimp [A] at hbound ⊢
    by_contra hn
    have hneg := mul_neg_of_pos_of_neg hj₀ (lt_of_not_ge hn)
    nlinarith
  have hnonneg : 0 ≤ (splitPolynomial j r - r ^ 2 / 2) -
      (splitPolynomial j a - a ^ 2 / 2) := by
    rw [polynomial_difference j (by omega)]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr har) hfactor) (by positivity)
  linarith

/-- The uppermost relevant branch stops exactly at `4/13`. -/
theorem top_cell_monotone : MonotoneOn adjustedSplit (Icc (1 / 4 : ℝ) (4 / 13)) := by
  intro a ha r hr har
  have ha' : a ∈ Icc (1 / ((2 : ℝ) + 2)) (1 / ((2 : ℝ) + 1)) := by
    norm_num
    constructor <;> linarith [ha.1, ha.2]
  have hr' : r ∈ Icc (1 / ((2 : ℝ) + 2)) (1 / ((2 : ℝ) + 1)) := by
    norm_num
    constructor <;> linarith [hr.1, hr.2]
  unfold adjustedSplit
  rw [splitValue_on_cell 2 ha', splitValue_on_cell 2 hr']
  norm_num [splitPolynomial]
  have hprod := mul_nonneg (sub_nonneg.mpr har)
    (show 0 ≤ 8 - 13 * (r + a) by linarith [ha.2, hr.2])
  nlinarith

/-- Finitely many neighboring cells suffice above every positive reciprocal cutoff. -/
theorem adjustedSplit_monotone_above (n : ℕ) :
    MonotoneOn adjustedSplit (Icc (1 / ((n : ℝ) + 4)) (4 / 13)) := by
  induction n with
  | zero => simpa using top_cell_monotone
  | succ n ih =>
    have hcell : MonotoneOn adjustedSplit
        (Icc (1 / ((n : ℝ) + 5)) (1 / ((n : ℝ) + 4))) := by
      intro a ha r hr har
      have ha' : a ∈ Icc (1 / (((n + 3 : ℕ) : ℝ) + 2))
          (1 / (((n + 3 : ℕ) : ℝ) + 1)) := by
        convert ha using 1
        norm_num [Nat.cast_add, add_assoc]
      have hr' : r ∈ Icc (1 / (((n + 3 : ℕ) : ℝ) + 2))
          (1 / (((n + 3 : ℕ) : ℝ) + 1)) := by
        convert hr using 1
        norm_num [Nat.cast_add, add_assoc]
      unfold adjustedSplit
      rw [splitValue_on_cell (n + 3) ha', splitValue_on_cell (n + 3) hr']
      apply polynomial_monotone (n + 3 + 1) (by omega) _ _ har
      · convert ha using 1
        norm_num [Nat.cast_add, add_assoc]
      · convert hr using 1
        norm_num [Nat.cast_add, add_assoc]
    have hlo : 1 / ((n : ℝ) + 5) ≤ 1 / ((n : ℝ) + 4) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have hhi : 1 / ((n : ℝ) + 4) ≤ (4 / 13 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hmono := hcell.union_right ih (isGreatest_Icc hlo) (isLeast_Icc hhi)
    rw [Icc_union_Icc_eq_Icc hlo hhi] at hmono
    convert hmono using 1
    norm_num [Nat.cast_add, add_assoc]

/-- The dense-interval split comparison includes every intervening reciprocal junction. -/
theorem split_difference_bound {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (hr : r ≤ 4 / 13) :
    (r ^ 2 - a ^ 2) / 2 ≤ splitValue r - splitValue a := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
  have hlo : 1 / ((n : ℝ) + 4) ≤ a := by
    apply le_trans _ hn.le
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have h := adjustedSplit_monotone_above n ⟨hlo, har.trans hr⟩ ⟨hlo.trans har, hr⟩ har
  unfold adjustedSplit at h
  linarith

/-- A collision-corrected estimate is bounded by the split value at total square mass. -/
theorem collision_bound_le_split {a r q C : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hr : r ≤ 4 / 13) (hq : r ^ 2 = a ^ 2 + q)
    (hC : C ≤ splitValue a + q / 2) : C ≤ splitValue r := by
  have h := split_difference_bound ha har hr
  linarith

/-- On the dense interval the benchmark contains the split branch. -/
theorem split_le_benchmark_dense {d : ℝ} (hd : 153 / 338 ≤ d) (hhalf : d ≤ 1 / 2) :
    splitValue (Real.sqrt (1 - 2 * d)) ≤ benchmark d := by
  by_cases heq : d = 1 / 2
  · subst d
    norm_num [splitValue]
  have hd' : 1 / 4 < d := by linarith
  have hhalf' : d < 1 / 2 := lt_of_le_of_ne hhalf heq
  have hsqrt : Real.sqrt 21 < 5 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
    have hn := Real.sqrt_nonneg (21 : ℝ)
    nlinarith
  have he : 1 / 2 - d ≤ epsilonStar := by
    unfold epsilonStar
    linarith
  unfold benchmark
  rw [ite_eq_right (not_le.mpr hd'), ite_eq_left hhalf']
  have hm : mixedCurve (1 / 2 - d) = splitValue (Real.sqrt (1 - 2 * d)) := by
    unfold mixedCurve
    rw [ite_eq_left he]
    congr 2
    ring
  rw [hm]
  exact le_max_left _ _

/-- The scalar dense-interval consequence needed after finite multipartite anchoring. -/
theorem collision_bound_le_benchmark {a r q C : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hr : r ≤ 4 / 13) (hq : r ^ 2 = a ^ 2 + q)
    (hC : C ≤ splitValue a + q / 2) : C ≤ benchmark ((1 - r ^ 2) / 2) := by
  have hr₀ : 0 < r := ha.trans_le har
  have hd : 153 / 338 ≤ (1 - r ^ 2) / 2 := by nlinarith
  have hhalf : (1 - r ^ 2) / 2 ≤ 1 / 2 := by nlinarith [sq_nonneg r]
  have h := split_le_benchmark_dense hd hhalf
  have heq : Real.sqrt (1 - 2 * ((1 - r ^ 2) / 2)) = r := by
    rw [show 1 - 2 * ((1 - r ^ 2) / 2) = r ^ 2 by ring, Real.sqrt_sq hr₀.le]
  rw [heq] at h
  exact (collision_bound_le_split ha har hr hq hC).trans h

end Erdos1017.DenseMultipartite
