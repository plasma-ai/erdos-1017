module

public import Erdos1017.Models.Capped.CappedColorConfiguration

/-!
# Vanishing clique violation of feasible charge matrices

A feasible finite charge matrix makes the full-clique test vanish
(`violation_eq_zero_of_configuration_dualFeasible`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.CappedModel

open scoped BigOperators

variable {k : ℕ}

/-- An actually feasible finite charge matrix makes the full-clique test vanish. -/
theorem violation_eq_zero_of_configuration_dualFeasible
    (c : CliquePair k → CappedColor)
    (hc : WeightedGraph.DualFeasible (configurationGraph c) (chargeMatrix c)) :
    violation c = 0 := by
  classical
  by_cases hz : ∃ p, CappedColor.adjacency (c p) = 0
  · obtain ⟨p, hp⟩ := hz
    have hprod : (∏ q, CappedColor.adjacency (c q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) hp
    simp only [violation, hprod, mul_zero]
  · have hA (p : CliquePair k) : CappedColor.adjacency (c p) = 1 :=
      (CappedColor.adjacency_eq_zero_or_one _).resolve_left (fun hp => hz ⟨p, hp⟩)
    have hclique : (configurationGraph c).IsClique
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
      intro i _ j _ hij
      change CappedColor.adjacency (pairColor c i j) = 1
      rcases lt_or_gt_of_ne hij with h | h
      · rw [pairColor_lt c i j h]
        exact hA _
      · rw [pairColor_symm, pairColor_lt c j i h]
        exact hA _
    have hcharge := hc.2.2 Finset.univ hclique
    have hobj : WeightedGraph.charge (chargeMatrix c) Finset.univ =
        WeightedGraph.objective (fun _ => 1) (chargeMatrix c) := by
      simp [WeightedGraph.charge_eq_sum, WeightedGraph.objective]
    rw [hobj, chargeMatrix_objective] at hcharge
    simp only [violation, hA, Finset.prod_const_one, mul_one,
      max_eq_right (sub_nonpos.mpr hcharge)]

end Erdos1017.CappedModel
