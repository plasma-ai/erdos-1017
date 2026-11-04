module

public import Erdos1017.LowerBound.FractionalBipartite

/-!
# Signed duals of weighted graphs

A dual is feasible (`DualFeasible`) when its signed edge coefficients vanish off
the graph and are constrained on cliques; its objective is bounded by the value,
and pulling a feasible dual back through independent clones preserves every
clique inequality.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators
open FractionalGraph

variable {n m : ℕ}

/-- Half the ordered-pair sum counts each unordered clique edge once. -/
def charge (y : Fin n → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i, ∑ j, if i ∈ S ∧ j ∈ S then y i j else 0) / 2

def objective (w : Fin n → ℝ) (y : Fin n → Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, y i j * (w i * w j)) / 2

/-- Signed edge coefficients vanish off the graph and are constrained only on actual cliques. -/
def DualFeasible (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, y i j = y j i) ∧ (∀ i j, ¬G.Adj i j → y i j = 0) ∧
    ∀ S : Finset (Fin n), G.IsClique (S : Set (Fin n)) → charge y S ≤ 1

theorem charge_eq_sum (y : Fin n → Fin n → ℝ) (S : Finset (Fin n)) :
    charge y S = (∑ i ∈ S, ∑ j ∈ S, y i j) / 2 := by
  have hterm (i j : Fin n) : (if i ∈ S ∧ j ∈ S then y i j else 0) =
      if i ∈ S then (if j ∈ S then y i j else 0) else 0 := by
    split_ifs <;> simp_all
  simp only [charge, hterm, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem weighted_charge_identity (y : Fin n → Fin n → ℝ) (w : Finset (Fin n) → ℝ) :
    (∑ S, w S * charge y S) = (∑ i, ∑ j, y i j * pairLoad w i j) / 2 := by
  simp only [charge, mul_div, Finset.mul_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairLoad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> ring

theorem dual_objective_le_subset_cost (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ)
    (hy : DualFeasible G y) (w : Finset (Fin n) → ℝ) (hw : SubsetFeasible G w) :
    objective (fun _ => 1) y ≤ ∑ S, w S := by
  have hcharge : objective (fun _ => 1) y = ∑ S, w S * charge y S := by
    rw [weighted_charge_identity]
    unfold objective
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.Adj i j
    · simp [hw.2.2 i j hij]
    · simp [hy.2.1 i j hij]
  rw [hcharge]
  apply Finset.sum_le_sum
  intro S _
  by_cases hz : w S = 0
  · simp [hz]
  · have hS := hw.2.1 S hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hy.2.2 S hS.2) (hw.1 S)

theorem dual_objective_le_value (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ)
    (hy : DualFeasible G y) : objective (fun _ => 1) y ≤ value G := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  rw [value_eq_optimal G w hw hmin]
  have h := dual_objective_le_subset_cost G y hy (extendWeights G w) (extendWeights_feasible G w hw)
  have hcost := extendWeights_sum G w (fun _ => 1)
  simp only [mul_one] at hcost
  simpa only [hcost, FinitePrimal.cost] using h

theorem image_clique_of_comap (G : SimpleGraph (Fin n)) (π : Fin m → Fin n)
    (S : Finset (Fin m)) (hS : (G.comap π).IsClique (S : Set (Fin m))) :
    G.IsClique (S.image π : Set (Fin n)) := by
  intro i hi j hj hij
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
  exact hS hu hv (fun h => hij (congrArg π h))

theorem injective_on_comap_clique (G : SimpleGraph (Fin n)) (π : Fin m → Fin n)
    (S : Finset (Fin m)) (hS : (G.comap π).IsClique (S : Set (Fin m))) :
    Set.InjOn π (S : Set (Fin m)) := by
  intro i hi j hj heq
  by_contra hij
  have h := hS hi hj hij
  change G.Adj (π i) (π j) at h
  rw [heq] at h
  exact G.irrefl h

theorem charge_comap (G : SimpleGraph (Fin n)) (π : Fin m → Fin n)
    (y : Fin n → Fin n → ℝ) (S : Finset (Fin m))
    (hS : (G.comap π).IsClique (S : Set (Fin m))) :
    charge (fun i j => y (π i) (π j)) S = charge y (S.image π) := by
  rw [charge_eq_sum, charge_eq_sum]
  rw [Finset.sum_image (injective_on_comap_clique G π S hS)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.sum_image (injective_on_comap_clique G π S hS)).symm

/-- Pulling a feasible dual back through independent clones preserves every clique inequality. -/
theorem dualFeasible_comap (G : SimpleGraph (Fin n)) (π : Fin m → Fin n)
    (y : Fin n → Fin n → ℝ) (hy : DualFeasible G y) :
    DualFeasible (G.comap π) (fun i j => y (π i) (π j)) := by
  refine ⟨fun i j => hy.1 _ _, fun i j hij => hy.2.1 _ _ hij, ?_⟩
  intro S hS
  rw [charge_comap G π y S hS]
  exact hy.2.2 _ (image_clique_of_comap G π S hS)

end Erdos1017.WeightedGraph
