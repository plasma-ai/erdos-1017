module

public import Erdos1017.LowerBound.WeightedGraphLimit

/-!
# Finite weighted graphs and the density limit

This module defines the objective, clique charge and density of a weighted graph
on a finite index type, and shows that a probability weighting with a symmetric
charge supported on the edges and at most one on every clique has objective at
most the density limit at its density (`finite_objective_le_densityLimit`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteObjective (w : ι → ℝ) (y : ι → ι → ℝ) : ℝ :=
  (∑ i, ∑ j, y i j * (w i * w j)) / 2

def finiteCharge (y : ι → ι → ℝ) (S : Finset ι) : ℝ := (∑ i ∈ S, ∑ j ∈ S, y i j) / 2

def finiteDensity (G : SimpleGraph ι) (w : ι → ℝ) : ℝ := by
  classical
  exact finiteObjective w (fun i j => if G.Adj i j then 1 else 0)

omit [DecidableEq ι] in
theorem objective_relabel (e : ι ≃ Fin (Fintype.card ι)) (w : ι → ℝ) (y : ι → ι → ℝ) :
    objective (fun i => w (e.symm i)) (fun i j => y (e.symm i) (e.symm j)) = finiteObjective w y := by
  unfold objective finiteObjective
  rw [← Equiv.sum_comp e]
  simp_rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply]

/-- The weighted-base bound is invariant under an arbitrary finite vertex labeling. -/
theorem finite_objective_le_densityLimit (G : SimpleGraph ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (y : ι → ι → ℝ)
    (hsymm : ∀ i j, y i j = y j i) (hsupport : ∀ i j, ¬G.Adj i j → y i j = 0)
    (hcharge : ∀ S : Finset ι, G.IsClique (S : Set ι) → finiteCharge y S ≤ 1) :
    finiteObjective w y ≤ FractionalGraph.densityLimit (finiteDensity G w) := by
  classical
  let e := Fintype.equivFin ι
  let H := G.comap e.symm
  let z : Fin (Fintype.card ι) → Fin (Fintype.card ι) → ℝ := fun i j => y (e.symm i) (e.symm j)
  have hsum' : (∑ i : Fin (Fintype.card ι), w (e.symm i)) = 1 := by
    rw [← Equiv.sum_comp e]
    simpa only [Equiv.symm_apply_apply] using hsum
  have hz : DualFeasible H z := by
    refine ⟨fun i j => hsymm _ _, fun i j hij => hsupport _ _ hij, ?_⟩
    intro S hS
    have hclique : G.IsClique (S.image e.symm : Set ι) := by
      intro i hi j hj hij
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
      exact hS hu hv (fun h => hij (congrArg e.symm h))
    have heq : charge z S = finiteCharge y (S.image e.symm) := by
      rw [charge_eq_sum]
      unfold finiteCharge
      rw [Finset.sum_image (fun _ _ _ _ h => e.symm.injective h)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_image (fun _ _ _ _ h => e.symm.injective h)).symm
    rw [heq]
    exact hcharge _ hclique
  have h := objective_le_densityLimit H (fun i => w (e.symm i)) (fun i => hw _) hsum' z hz
  rw [objective_relabel e w y] at h
  have hden : density H (fun i => w (e.symm i)) = finiteDensity G w := by
    exact objective_relabel e w (fun i j => if G.Adj i j then 1 else 0)
  rwa [hden] at h

end Erdos1017.WeightedGraph
