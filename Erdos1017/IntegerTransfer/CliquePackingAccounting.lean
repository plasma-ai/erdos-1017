module

public import Erdos1017.IntegerTransfer.CliquePackingCompletion
public import Erdos1017.IntegerTransfer.FractionalCliqueTruncation

/-!
# Edge accounting for clique packings

The uncovered-edge count of a clique packing is exactly the original count minus
all packed clique pairs, so every packed clique saves its number of edges minus
one in the final integer partition (`cliquePartitionNumber_le_edge_savings`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017

open scoped BigOperators
open FractionalGraph

variable {n : ℕ}

theorem partition_indicator_feasible (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : G.IsCliqueEdgePartition P) :
    SubsetFeasible G (fun S => if S ∈ P then 1 else 0) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro S
    dsimp
    split_ifs <;> norm_num
  · intro S hS
    have hmem : S ∈ P := by by_contra h; simp [h] at hS
    exact hP.1 S hmem
  · intro u v huv
    obtain ⟨S, ⟨hS, hu, hv⟩, huniq⟩ := hP.2 u v huv
    unfold pairLoad
    rw [Finset.sum_eq_single S]
    · simp [hS, hu, hv]
    · intro T _ hTS
      by_cases hT : T ∈ P
      · have hnot : ¬(u ∈ T ∧ v ∈ T) := by
          intro h
          exact hTS (huniq T ⟨hT, h⟩)
        simp [hnot]
      · simp [hT]
    · simp

theorem partition_pair_count (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : G.IsCliqueEdgePartition P) : (∑ S ∈ P, S.card.choose 2) = G.edgeSet.ncard := by
  classical
  have h := subset_pair_mass G (fun S => if S ∈ P then 1 else 0) (partition_indicator_feasible G P hP)
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at h
  exact_mod_cast h

theorem packing_disjoint_residual_partition (G : SimpleGraph (Fin n))
    (P Q : Finset (Finset (Fin n))) (hP : IsCliqueEdgePacking G P)
    (hQ : (packingResidual G P).IsCliqueEdgePartition Q) : Disjoint P Q := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hSP hSQ
  obtain ⟨u, hu, v, hv, huv⟩ := (Finset.one_lt_card (s := S)).mp (by have := (hP.1 S hSP).1; omega)
  have hres := (hQ.1 S hSQ).2 hu hv huv
  exact ((packingResidual_adj G P u v).mp hres).2 ⟨S, hSP, hu, hv⟩

/-- The uncovered-edge count is exactly the original count minus all packed clique pairs. -/
theorem packing_residual_pair_count (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n)))
    (hP : IsCliqueEdgePacking G P) :
    (∑ S ∈ P, S.card.choose 2) + (packingResidual G P).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQ, _⟩ := (packingResidual G P).exists_isCliqueEdgePartition_card_eq
  have hcount := partition_pair_count G (P ∪ Q) (packing_union_partition G P Q hP hQ)
  rw [Finset.sum_union (packing_disjoint_residual_partition G P Q hP hQ),
    partition_pair_count _ Q hQ] at hcount
  exact hcount

/-- Every selected clique saves its number of edges minus one in the final integer partition. -/
theorem cliquePartitionNumber_le_edge_savings (G : SimpleGraph (Fin n))
    (P : Finset (Finset (Fin n))) (hP : IsCliqueEdgePacking G P) :
    (cliquePartitionNumber G : ℝ) ≤ (G.edgeSet.ncard : ℝ) -
      ∑ S ∈ P, ((S.card.choose 2 : ℝ) - 1) := by
  have hcost := cliquePartitionNumber_le_packing_cost G P hP
  have hcount := packing_residual_pair_count G P hP
  have hcost' : (cliquePartitionNumber G : ℝ) ≤ P.card + (packingResidual G P).edgeSet.ncard := by
    exact_mod_cast hcost
  have hcount' : (∑ S ∈ P, (S.card.choose 2 : ℝ)) + (packingResidual G P).edgeSet.ncard =
      (G.edgeSet.ncard : ℝ) := by exact_mod_cast hcount
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

end Erdos1017
