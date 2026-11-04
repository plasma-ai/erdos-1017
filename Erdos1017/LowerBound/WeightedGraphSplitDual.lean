module

public import Erdos1017.LowerBound.FiniteWeightedGraph
public import Erdos1017.LowerBound.Repeat

/-!
# One-head split dual

The one-head matrix (`oneHeadMatrix`) is symmetric with explicit diagonal,
objective and charge, and an integer quadratic inequality proves all finite
clique constraints for the split family (`split_charge_le_one`), giving the
split finite lower bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oneHeadMatrix (A B : ℝ) : Option ι → Option ι → ℝ
  | none, none => 0
  | none, some _ => A
  | some _, none => A
  | some i, some j => if i = j then 0 else B

theorem offDiagonal_sum (w : ι → ℝ) :
    (∑ i, ∑ j, if i = j then 0 else w i * w j) = (∑ i, w i) ^ 2 - ∑ i, w i ^ 2 := by
  have hterm (i j : ι) : (if i = j then 0 else w i * w j) =
      w i * w j - if i = j then w i ^ 2 else 0 := by
    split_ifs with hij
    · subst j; ring
    · simp
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_mul_sum]
  ring

theorem oneHead_objective (A B : ℝ) (w : Option ι → ℝ) :
    finiteObjective w (oneHeadMatrix A B) =
      A * w none * (∑ i, w (some i)) +
        B * ((∑ i, w (some i)) ^ 2 - ∑ i, w (some i) ^ 2) / 2 := by
  unfold finiteObjective
  simp only [Fintype.sum_option, oneHeadMatrix, zero_mul, zero_add,
    Finset.sum_add_distrib]
  have htail : (∑ i : ι, ∑ j : ι, (if i = j then (0 : ℝ) else B) *
      (w (some i) * w (some j))) =
      B * ((∑ i, w (some i)) ^ 2 - ∑ i, w (some i) ^ 2) := by
    rw [← offDiagonal_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [htail]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  ring

theorem finiteCharge_eq_objective (y : ι → ι → ℝ) (S : Finset ι) :
    finiteCharge y S = finiteObjective (fun i => if i ∈ S then 1 else 0) y := by
  unfold finiteCharge finiteObjective
  have hterm (i j : ι) : y i j * ((if i ∈ S then (1 : ℝ) else 0) *
      (if j ∈ S then (1 : ℝ) else 0)) =
      if i ∈ S then (if j ∈ S then y i j else 0) else 0 := by
    split_ifs <;> ring
  simp only [hterm, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem oneHead_charge (A B : ℝ) (S : Finset (Option ι)) :
    finiteCharge (oneHeadMatrix A B) S =
      A * (if none ∈ S then 1 else 0) *
          ((Finset.univ.filter fun i : ι => some i ∈ S).card : ℝ) +
        B * (((Finset.univ.filter fun i : ι => some i ∈ S).card : ℝ) ^ 2 -
          ((Finset.univ.filter fun i : ι => some i ∈ S).card : ℝ)) / 2 := by
  rw [finiteCharge_eq_objective, oneHead_objective]
  simp only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_boole]

omit [Fintype ι] in
theorem oneHeadMatrix_symm (A B : ℝ) (i j : Option ι) :
    oneHeadMatrix A B i j = oneHeadMatrix A B j i := by
  cases i <;> cases j <;> simp [oneHeadMatrix, eq_comm]

omit [Fintype ι] in
@[simp] theorem oneHeadMatrix_diag (A B : ℝ) (i : Option ι) : oneHeadMatrix A B i i = 0 := by
  cases i <;> simp [oneHeadMatrix]

/-- The integer quadratic inequality proves all finite clique constraints for the split family. -/
theorem split_charge_le_one (j : ℕ) (hj : 0 < j) (S : Finset (Option ι)) :
    finiteCharge (oneHeadMatrix (2 / ((j : ℝ) + 1)) (-2 / ((j : ℝ) * ((j : ℝ) + 1)))) S ≤ 1 := by
  rw [oneHead_charge]
  let k := (Finset.univ.filter fun i : ι => some i ∈ S).card
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hden : 0 < (j : ℝ) * ((j : ℝ) + 1) := by positivity
  by_cases hhead : none ∈ S
  · simp only [ite_eq_left hhead, mul_one]
    have h := Repeat.discrete_quadratic_bound j k
    have heq : 2 / ((j : ℝ) + 1) * (k : ℝ) +
        -2 / ((j : ℝ) * ((j : ℝ) + 1)) * ((k : ℝ) ^ 2 - (k : ℝ)) / 2 =
        ((k : ℝ) * (2 * (j : ℝ) + 1 - (k : ℝ))) / ((j : ℝ) * ((j : ℝ) + 1)) := by
      field_simp
      ring
    change 2 / ((j : ℝ) + 1) * (k : ℝ) +
      -2 / ((j : ℝ) * ((j : ℝ) + 1)) * ((k : ℝ) ^ 2 - (k : ℝ)) / 2 ≤ 1
    rw [heq, div_le_one hden]
    exact h
  · simp only [ite_eq_right hhead, mul_zero, zero_mul, zero_add]
    have hk := Repeat.pairs_nonneg k
    have hpair : 0 ≤ (k : ℝ) ^ 2 - (k : ℝ) := by
      unfold Repeat.pairs at hk
      nlinarith
    have hneg : -2 / ((j : ℝ) * ((j : ℝ) + 1)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le
    have h := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hpair)
      (by norm_num : (0 : ℝ) ≤ 2)
    exact h.trans (by norm_num)

theorem split_finite_lower (j : ℕ) (hj : 0 < j) (w : Option ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    2 / ((j : ℝ) + 1) * w none * (∑ i, w (some i)) +
      (-2 / ((j : ℝ) * ((j : ℝ) + 1))) *
        ((∑ i, w (some i)) ^ 2 - ∑ i, w (some i) ^ 2) / 2 ≤
      FractionalGraph.densityLimit (finiteDensity (⊤ : SimpleGraph (Option ι)) w) := by
  have h := finite_objective_le_densityLimit (⊤ : SimpleGraph (Option ι)) w hw hsum
    (oneHeadMatrix (2 / ((j : ℝ) + 1)) (-2 / ((j : ℝ) * ((j : ℝ) + 1))))
    (oneHeadMatrix_symm _ _) (fun i j hij => by
      have heq : i = j := by simpa only [SimpleGraph.top_adj, not_not] using hij
      subst j
      exact oneHeadMatrix_diag _ _ _)
    (fun S _ => split_charge_le_one j hj S)
  rwa [oneHead_objective] at h

end Erdos1017.WeightedGraph
