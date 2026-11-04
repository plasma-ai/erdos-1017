module

public import Erdos1017.LowerBound.WeightedGraphLeafDual

/-!
# Two-head and leaf lower bounds in the limit

With the two-head tail weights, the complete two-head signed dual and the
extra-leaf split dual both survive the finite-tail limit
(`complete_twoHead_limit_lower`, `leaf_limit_lower`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators Topology
open Filter FractionalGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def twoHeadWeights (a b u : ℝ) (N : ℕ) : Option (Option (Fin (N + 1))) → ℝ
  | none => a
  | some i => equalTailWeights b u N i

theorem twoHeadWeights_tail_sum (a b u : ℝ) (N : ℕ) :
    (∑ i, twoHeadWeights a b u N (some (some i))) = u := equalTailWeights_tail_sum b u N

theorem twoHeadWeights_tail_square_sum (a b u : ℝ) (N : ℕ) :
    (∑ i, twoHeadWeights a b u N (some (some i)) ^ 2) = u ^ 2 / ((N + 1 : ℕ) : ℝ) :=
  equalTailWeights_tail_square_sum b u N

theorem twoHeadWeights_nonneg (a b u : ℝ) (N : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (i : Option (Option (Fin (N + 1)))) : 0 ≤ twoHeadWeights a b u N i := by
  cases i with
  | none => exact ha
  | some i => cases i with
    | none => exact hb
    | some i => exact div_nonneg hu (Nat.cast_nonneg _)

theorem twoHeadWeights_sum (a b u : ℝ) (N : ℕ) (hsum : a + b + u = 1) :
    (∑ i, twoHeadWeights a b u N i) = 1 := by
  rw [Fintype.sum_option, Fintype.sum_option, twoHeadWeights_tail_sum]
  change a + (b + u) = 1
  linarith

theorem leaf_density (w : Option (Option ι) → ℝ) :
    finiteDensity (leafGraph : SimpleGraph (Option (Option ι))) w =
      w none * w (some none) + w (some none) * (∑ i, w (some (some i))) +
        ((∑ i, w (some (some i))) ^ 2 - ∑ i, w (some (some i)) ^ 2) / 2 := by
  classical
  have hmat (i j : Option (Option ι)) :
      (if (leafGraph : SimpleGraph (Option (Option ι))).Adj i j then (1 : ℝ) else 0) =
        twoHeadMatrix 1 0 1 1 i j := by
    cases i with
    | none =>
      cases j with
      | none => simp [leafGraph, twoHeadMatrix, adjoinHeadMatrix]
      | some j => cases j <;> simp [leafGraph, twoHeadMatrix, adjoinHeadMatrix]
    | some i =>
      cases j with
      | none => cases i <;> simp [leafGraph, twoHeadMatrix, adjoinHeadMatrix]
      | some j =>
        simp only [leafGraph, Option.some.injEq, reduceCtorEq, false_implies, and_true,
          twoHeadMatrix, adjoinHeadMatrix]
        cases i <;> cases j <;> simp [oneHeadMatrix, ite_not]
  unfold finiteDensity
  simp_rw [hmat]
  rw [twoHead_objective]
  ring

theorem complete_twoHead_finite_lower (w : Option (Option ι) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    finiteObjective w (twoHeadMatrix 1 (2 / 3) (-2 / 3) (-1 / 3)) ≤
      densityLimit (finiteDensity (⊤ : SimpleGraph (Option (Option ι))) w) :=
  finite_objective_le_densityLimit ⊤ w hw hsum _ (twoHeadMatrix_symm _ _ _ _)
    (fun i j hij => by
      have heq : i = j := by simpa only [SimpleGraph.top_adj, not_not] using hij
      subst j
      exact twoHeadMatrix_diag _ _ _ _ _) (fun S _ => complete_twoHead_charge_le_one S)

private theorem tail_limit (L d B u : ℝ)
    (h : ∀ N : ℕ, L - B * (u ^ 2 / ((N + 1 : ℕ) : ℝ)) ≤
      densityLimit (d - (u ^ 2 / ((N + 1 : ℕ) : ℝ)) / 2)) : L ≤ densityLimit d := by
  have hvanish : Tendsto (fun N : ℕ => u ^ 2 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (u ^ 2)
  have hL : Tendsto (fun _ : ℕ => L) atTop (𝓝 L) := tendsto_const_nhds
  have hd : Tendsto (fun _ : ℕ => d) atTop (𝓝 d) := tendsto_const_nhds
  have hleft := hL.sub (hvanish.const_mul B)
  have hright := densityLimit_continuous.continuousAt.tendsto.comp (hd.sub (hvanish.div_const 2))
  simpa only [mul_zero, zero_div, sub_zero] using le_of_tendsto_of_tendsto' hleft hright h

/-- The complete two-head signed dual survives the finite-tail limit. -/
theorem complete_twoHead_limit_lower (a b u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hsum : a + b + u = 1) :
    a * b + (2 / 3) * (a - b) * u - u ^ 2 / 6 ≤ densityLimit ((1 - a ^ 2 - b ^ 2) / 2) := by
  apply tail_limit _ _ (-1 / 6) u
  intro N
  have h := complete_twoHead_finite_lower (twoHeadWeights a b u N)
    (twoHeadWeights_nonneg a b u N ha hb hu) (twoHeadWeights_sum a b u N hsum)
  rw [twoHead_objective, twoHeadWeights_tail_sum, twoHeadWeights_tail_square_sum,
    finiteDensity_top, twoHeadWeights_sum a b u N hsum, Fintype.sum_option,
    Fintype.sum_option, twoHeadWeights_tail_square_sum] at h
  simp only [twoHeadWeights, equalTailWeights, one_pow, one_mul] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The extra-leaf split dual survives the finite-tail limit. -/
theorem leaf_limit_lower (j : ℕ) (hj : 0 < j) (a b u : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hsum : a + b + u = 1) :
    a * b + 2 / ((j : ℝ) + 1) * b * u - u ^ 2 / ((j : ℝ) * ((j : ℝ) + 1)) ≤
      densityLimit (a * b + b * u + u ^ 2 / 2) := by
  apply tail_limit _ _ (-1 / ((j : ℝ) * ((j : ℝ) + 1))) u
  intro N
  have h := leaf_finite_lower j hj (twoHeadWeights a b u N)
    (twoHeadWeights_nonneg a b u N ha hb hu) (twoHeadWeights_sum a b u N hsum)
  rw [twoHead_objective, leaf_density, twoHeadWeights_tail_sum, twoHeadWeights_tail_square_sum] at h
  simp only [twoHeadWeights, equalTailWeights, one_mul, zero_mul, zero_add] at h
  convert h using 1 <;> congr 1 <;> ring

end Erdos1017.WeightedGraph
