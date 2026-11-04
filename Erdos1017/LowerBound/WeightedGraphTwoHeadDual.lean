module

public import Erdos1017.LowerBound.WeightedGraphSplitLower

/-!
# Two-head dual matrices

Adjoining a head to a matrix and the two-head matrix (`twoHeadMatrix`) have
explicit objective and charge, and all natural tail counts satisfy the signed
complete two-head family inequalities (`complete_twoHead_charge_le_one`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def adjoinHeadMatrix (v : ι → ℝ) (y : ι → ι → ℝ) : Option ι → Option ι → ℝ
  | none, none => 0
  | none, some i => v i
  | some i, none => v i
  | some i, some j => y i j

omit [DecidableEq ι] in
theorem adjoinHead_objective (v : ι → ℝ) (y : ι → ι → ℝ) (w : Option ι → ℝ) :
    finiteObjective w (adjoinHeadMatrix v y) =
      w none * (∑ i, v i * w (some i)) + finiteObjective (fun i => w (some i)) y := by
  unfold finiteObjective
  simp only [Fintype.sum_option, adjoinHeadMatrix, zero_mul, zero_add, Finset.sum_add_distrib]
  have h₁ : (∑ i, v i * (w (some i) * w none)) = w none * ∑ i, v i * w (some i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h₂ : (∑ i, v i * (w none * w (some i))) = w none * ∑ i, v i * w (some i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h₁, h₂]
  ring

def twoHeadMatrix (E A B C : ℝ) : Option (Option ι) → Option (Option ι) → ℝ :=
  adjoinHeadMatrix (fun i => match i with | none => E | some _ => A) (oneHeadMatrix B C)

theorem twoHead_objective (E A B C : ℝ) (w : Option (Option ι) → ℝ) :
    finiteObjective w (twoHeadMatrix E A B C) =
      E * w none * w (some none) +
        (A * w none + B * w (some none)) * (∑ i, w (some (some i))) +
        C * ((∑ i, w (some (some i))) ^ 2 - ∑ i, w (some (some i)) ^ 2) / 2 := by
  rw [twoHeadMatrix, adjoinHead_objective, oneHead_objective]
  simp only [Fintype.sum_option, ← Finset.mul_sum]
  ring

theorem twoHead_charge (E A B C : ℝ) (S : Finset (Option (Option ι))) :
    finiteCharge (twoHeadMatrix E A B C) S =
      E * (if none ∈ S then 1 else 0) * (if some none ∈ S then 1 else 0) +
        (A * (if none ∈ S then 1 else 0) + B * (if some none ∈ S then 1 else 0)) *
          ((Finset.univ.filter fun i : ι => some (some i) ∈ S).card : ℝ) +
        C * (((Finset.univ.filter fun i : ι => some (some i) ∈ S).card : ℝ) ^ 2 -
          ((Finset.univ.filter fun i : ι => some (some i) ∈ S).card : ℝ)) / 2 := by
  rw [finiteCharge_eq_objective, twoHead_objective]
  simp only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_boole]

omit [Fintype ι] in
theorem twoHeadMatrix_symm (E A B C : ℝ) (i j : Option (Option ι)) :
    twoHeadMatrix E A B C i j = twoHeadMatrix E A B C j i := by
  cases i <;> cases j <;> simp [twoHeadMatrix, adjoinHeadMatrix, oneHeadMatrix_symm]

omit [Fintype ι] in
@[simp] theorem twoHeadMatrix_diag (E A B C : ℝ) (i : Option (Option ι)) :
    twoHeadMatrix E A B C i i = 0 := by
  cases i <;> simp [twoHeadMatrix, adjoinHeadMatrix]

/-- All natural tail counts satisfy the signed complete two-head family inequalities. -/
theorem complete_twoHead_charge_le_one (S : Finset (Option (Option ι))) :
    finiteCharge (twoHeadMatrix 1 (2 / 3) (-2 / 3) (-1 / 3)) S ≤ 1 := by
  rw [twoHead_charge]
  let k := (Finset.univ.filter fun i : ι => some (some i) ∈ S).card
  have hpair := Repeat.pairs_nonneg k
  have hquad := Repeat.discrete_quadratic_bound 2 k
  norm_num at hquad
  unfold Repeat.pairs at hpair
  simp only [one_mul]
  change (if none ∈ S then (1 : ℝ) else 0) * (if some none ∈ S then 1 else 0) +
    (2 / 3 * (if none ∈ S then 1 else 0) + (-2 / 3) * (if some none ∈ S then 1 else 0)) *
      (k : ℝ) + (-1 / 3) * ((k : ℝ) ^ 2 - (k : ℝ)) / 2 ≤ 1
  split_ifs <;> nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

end Erdos1017.WeightedGraph
