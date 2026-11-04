module

public import Erdos1017.LowerBound.FractionalCanonicalLimit

/-!
# Endpoint values of the density limit

This module collects lemmas on the density limit and extremal function at
density zero and one half (`densityLimit_zero`, `densityLimit_half`), including
that the complete graph has value at most one.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators Topology
open Filter

theorem extremal_zero (n : ℕ) : extremal n 0 = 0 :=
  le_antisymm (by simpa using extremal_le n 0) (extremal_nonneg n 0)

theorem densityLimit_zero : densityLimit 0 = 0 := by
  have h := tendsto_extremal_of_density (fun _ => 0) (fun _ => Nat.zero_le _) 0
    (by simp)
  simp only [extremal_zero, zero_div] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem finiteEdges_top_card (n : ℕ) : (finiteEdges (⊤ : SimpleGraph (Fin n))).card = n.choose 2 := by
  classical
  have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 1
  ext e
  simp [finiteEdges]

theorem graph_eq_top_of_edge_count {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = n.choose 2) : G = ⊤ := by
  have hsub := finiteEdges_mono (show G ≤ ⊤ from le_top)
  have heq : finiteEdges G = finiteEdges ⊤ := Finset.eq_of_subset_of_card_le hsub (by
    rw [finiteEdges_top_card, finiteEdges_card, hG])
  apply SimpleGraph.edgeSet_injective
  ext e
  have hmem := congrArg (fun S => e ∈ S) heq
  simpa [finiteEdges] using hmem

theorem value_top_le_one (n : ℕ) (hn : 2 ≤ n) : value (⊤ : SimpleGraph (Fin n)) ≤ 1 := by
  let w : Finset (Fin n) → ℝ := fun S => if S = Finset.univ then 1 else 0
  have hw : SubsetFeasible (⊤ : SimpleGraph (Fin n)) w := by
    refine ⟨?_, ?_, ?_⟩
    · intro S
      simp only [w]
      split_ifs <;> norm_num
    · intro S hS
      have heq : S = Finset.univ := by
        by_contra hne
        exact hS (by simp [w, hne])
      subst S
      refine ⟨by simpa using hn, ?_⟩
      intro i _ j _ hij
      exact hij
    · intro i j _
      simpa [w] using pairLoad_single (Finset.univ : Finset (Fin n)) 1 i j
  have h := value_le_subset_cost _ w hw
  simpa [w] using h

theorem extremal_complete_le_one (n : ℕ) (hn : 2 ≤ n) : extremal n (n.choose 2) ≤ 1 := by
  obtain ⟨G, hG, hvG⟩ := extremal_attained n (n.choose 2) le_rfl
  rw [graph_eq_top_of_edge_count G hG] at hvG
  rw [← hvG]
  exact value_top_le_one n hn

theorem densityLimit_half : densityLimit (1 / 2) = 0 := by
  have h := tendsto_extremal_of_density (fun n => n.choose 2) (fun _ => le_rfl)
    (1 / 2) tendsto_complete_density
  have hzero : Tendsto (fun n : ℕ => extremal n (n.choose 2) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).squeeze'
      tendsto_inverse_square
    · exact Eventually.of_forall (fun n => div_nonneg (extremal_nonneg _ _) (sq_nonneg _))
    · filter_upwards [eventually_ge_atTop 2] with n hn
      exact div_le_div_of_nonneg_right (extremal_complete_le_one n hn) (sq_nonneg _)
  exact tendsto_nhds_unique h hzero

end Erdos1017.FractionalGraph
