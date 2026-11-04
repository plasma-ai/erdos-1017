module

public import Erdos1017.FractionalLimit.FractionalGraphProjection
public import Erdos1017.FractionalLimit.FractionalGraphChanges
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Edge counts of fractional graphs and their blowups

Two counting lemmas give the ordered edge count of a graph
(`ordered_edge_count`) and the edge count of a blowup (`edge_count_blowup`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n t : ℕ}

attribute [local instance] Classical.propDecidable

theorem ordered_edge_count (G : SimpleGraph (Fin n)) :
    (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (1 : ℕ) else 0) = 2 * G.edgeSet.ncard := by
  classical
  have hdegree (i : Fin n) : (∑ j : Fin n, if G.Adj i j then (1 : ℕ) else 0) = G.degree i := by
    rw [← G.card_neighborFinset_eq_degree]
    have hset : (Finset.univ.filter fun j => G.Adj i j) = G.neighborFinset i := by
      ext j
      simp
    simpa using congrArg Finset.card hset
  simp_rw [hdegree]
  rw [G.sum_degrees_eq_twice_card_edges]
  congr 1
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

theorem edge_count_blowup (G : SimpleGraph (Fin n)) (t : ℕ) :
    (blowup G t).edgeSet.ncard = t ^ 2 * G.edgeSet.ncard := by
  classical
  have hsum : (∑ u : Fin (n * t), ∑ v : Fin (n * t),
      if (blowup G t).Adj u v then (1 : ℕ) else 0) =
      t ^ 2 * (∑ i : Fin n, ∑ j : Fin n, if G.Adj i j then (1 : ℕ) else 0) := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp_rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Fintype.sum_prod_type]
    have hadj (i j : Fin n) (a b : Fin t) :
        (blowup G t).Adj (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) ↔ G.Adj i j := by
      change G.Adj (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
        (finProdFinEquiv.symm (finProdFinEquiv (j, b))).1 ↔ _
      simp only [Equiv.symm_apply_apply]
    simp only [hadj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    simp_rw [← Finset.mul_sum]
    ring
  rw [ordered_edge_count, ordered_edge_count] at hsum
  nlinarith [hsum]

end Erdos1017.FractionalGraph
