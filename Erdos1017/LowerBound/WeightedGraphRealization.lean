module

public import Erdos1017.LowerBound.WeightedGraphDual

/-!
# Blowup realizations of weighted bases

A realization replaces each base vertex `i` by `m i` independent vertices, with
zero multiplicities allowed; its edge count, density and objective are computed,
and every finite independent blowup gives the normalized weighted-base dual
bound.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.WeightedGraph

open scoped BigOperators
open FractionalGraph

variable {r : ℕ}

def cloneEquiv (m : Fin r → ℕ) : (Σ i : Fin r, Fin (m i)) ≃ Fin (∑ i, m i) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

def cloneProjection (m : Fin r → ℕ) (v : Fin (∑ i, m i)) : Fin r := ((cloneEquiv m).symm v).1

/-- Replace each base vertex `i` by `m i` independent vertices, allowing zero multiplicities. -/
def realization (G : SimpleGraph (Fin r)) (m : Fin r → ℕ) : SimpleGraph (Fin (∑ i, m i)) :=
  G.comap (cloneProjection m)

theorem sum_cloneProjection {R : Type*} [AddCommMonoid R] (m : Fin r → ℕ) (f : Fin r → R) :
    (∑ v : Fin (∑ i, m i), f (cloneProjection m v)) = ∑ i, m i • f i := by
  rw [← Equiv.sum_comp (cloneEquiv m)]
  simp only [cloneProjection, Equiv.symm_apply_apply, Fintype.sum_sigma,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem objective_realization (m : Fin r → ℕ) (y : Fin r → Fin r → ℝ) :
    objective (fun _ => 1) (fun u v => y (cloneProjection m u) (cloneProjection m v)) =
      objective (fun i => (m i : ℝ)) y := by
  simp only [objective, mul_one]
  rw [sum_cloneProjection m (fun i => ∑ v, y i (cloneProjection m v))]
  simp_rw [sum_cloneProjection, nsmul_eq_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def adjacencyMatrix (G : SimpleGraph (Fin r)) (i j : Fin r) : ℝ := by
  classical
  exact if G.Adj i j then 1 else 0

def density (G : SimpleGraph (Fin r)) (w : Fin r → ℝ) : ℝ := objective w (adjacencyMatrix G)

theorem adjacency_objective (G : SimpleGraph (Fin r)) :
    objective (fun _ => 1) (adjacencyMatrix G) = G.edgeSet.ncard := by
  classical
  have h := ordered_edge_count G
  have hreal : (∑ i : Fin r, ∑ j : Fin r, if G.Adj i j then (1 : ℝ) else 0) =
      2 * (G.edgeSet.ncard : ℝ) := by exact_mod_cast h
  simp only [objective, adjacencyMatrix, mul_one, hreal]
  ring

theorem realization_edge_count (G : SimpleGraph (Fin r)) (m : Fin r → ℕ) :
    ((realization G m).edgeSet.ncard : ℝ) = density G (fun i => (m i : ℝ)) := by
  rw [← adjacency_objective, density, ← objective_realization]
  rfl

theorem objective_div (w : Fin r → ℝ) (y : Fin r → Fin r → ℝ) (c : ℝ) :
    objective (fun i => w i / c) y = objective w y / c ^ 2 := by
  have hterm (i j : Fin r) : y i j * ((w i / c) * (w j / c)) =
      (y i j * (w i * w j)) / c ^ 2 := by ring
  unfold objective
  simp_rw [hterm, ← Finset.sum_div]
  ring

theorem realization_density (G : SimpleGraph (Fin r)) (m : Fin r → ℕ) :
    ((realization G m).edgeSet.ncard : ℝ) / ((∑ i, m i : ℕ) : ℝ) ^ 2 =
      density G (fun i => (m i : ℝ) / ((∑ i, m i : ℕ) : ℝ)) := by
  rw [realization_edge_count]
  exact (objective_div _ _ _).symm

theorem realization_objective_le_value (G : SimpleGraph (Fin r)) (m : Fin r → ℕ)
    (y : Fin r → Fin r → ℝ) (hy : DualFeasible G y) :
    objective (fun i => (m i : ℝ)) y ≤ value (realization G m) := by
  rw [← objective_realization]
  exact dual_objective_le_value _ _ (dualFeasible_comap G (cloneProjection m) y hy)

/-- Every finite independent blowup gives the normalized weighted-base dual bound. -/
theorem realization_objective_le_densityLimit (G : SimpleGraph (Fin r)) (m : Fin r → ℕ)
    (hm : 0 < ∑ i, m i) (y : Fin r → Fin r → ℝ) (hy : DualFeasible G y) :
    objective (fun i => (m i : ℝ) / ((∑ j, m j : ℕ) : ℝ)) y ≤
      densityLimit (density G (fun i => (m i : ℝ) / ((∑ j, m j : ℕ) : ℝ))) := by
  have h := finite_graph_le_densityLimit (realization G m) hm
    (((realization G m).edgeSet.ncard : ℝ) / ((∑ i, m i : ℕ) : ℝ) ^ 2)
  simp only [sub_self, abs_zero, mul_zero, sub_zero] at h
  rw [realization_density] at h
  rw [objective_div]
  exact (div_le_div_of_nonneg_right (realization_objective_le_value G m y hy) (sq_nonneg _)).trans h

theorem density_mem_Icc (G : SimpleGraph (Fin r)) (w : Fin r → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) : density G w ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hterm (i j : Fin r) : 0 ≤ adjacencyMatrix G i j * (w i * w j) ∧
      adjacencyMatrix G i j * (w i * w j) ≤ w i * w j := by
    unfold adjacencyMatrix
    split_ifs <;> simp [mul_nonneg (hw i) (hw j)]
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => (hterm i j).1))) (by norm_num)
  · have hbound : (∑ i, ∑ j, adjacencyMatrix G i j * (w i * w j)) ≤ 1 := by
      calc
        _ ≤ ∑ i, ∑ j, w i * w j := Finset.sum_le_sum (fun i _ =>
          Finset.sum_le_sum (fun j _ => (hterm i j).2))
        _ = 1 := by simp only [← Finset.mul_sum, hsum, mul_one]
    exact div_le_div_of_nonneg_right hbound (by norm_num)

end Erdos1017.WeightedGraph
