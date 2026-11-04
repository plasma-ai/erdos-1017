module

public import Erdos1017.IntegerTransfer.TransversalCliqueEdges
public import Erdos1017.IntegerTransfer.Nibble.HypergraphDegreePruning

/-!
# Degree and codegree bounds for the clique hypergraph

Incident hyperedges correspond bijectively to clique assignments, a graph edge
fixes two role values, and two distinct graph edges fix at least three, giving
deterministic maximum degree and codegree bounds for every clique hypergraph.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Incident hyperedges correspond bijectively to actual clique assignments. -/
theorem degree_eq (hk : 2 ≤ k) (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (v : Coordinate k A) :
    HypergraphNibble.degree (hypergraph G) v = ((assignments G).filter (fun X => v ∈ edges X)).card := by
  have hfilter : (hypergraph G).filter (fun e => v ∈ e) =
      ((assignments G).filter (fun X => v ∈ edges X)).image edges := by
    ext e
    simp only [hypergraph, Finset.mem_filter, Finset.mem_image]
    aesop
  unfold HypergraphNibble.degree
  rw [hfilter, Finset.card_image_of_injective _ (edges_injective hk)]

/-- The analogous correspondence for pairs of distinct graph-edge coordinates. -/
theorem codegree_eq (hk : 2 ≤ k) (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (v w : Coordinate k A) :
    HypergraphNibble.codegree (hypergraph G) v w =
      ((assignments G).filter (fun X => v ∈ edges X ∧ w ∈ edges X)).card := by
  have hfilter : (hypergraph G).filter (fun e => v ∈ e ∧ w ∈ e) =
      ((assignments G).filter (fun X => v ∈ edges X ∧ w ∈ edges X)).image edges := by
    ext e
    simp only [hypergraph, Finset.mem_filter, Finset.mem_image]
    aesop
  unfold HypergraphNibble.codegree
  rw [hfilter, Finset.card_image_of_injective _ (edges_injective hk)]

/-- A graph edge fixes two role values, giving the deterministic maximum degree. -/
theorem degree_le (hk : 2 ≤ k) (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (v : Coordinate k A) : HypergraphNibble.degree (hypergraph G) v ≤ Fintype.card A ^ (k - 2) := by
  rw [degree_eq hk]
  let F := (assignments G).filter (fun X => v ∈ edges X)
  by_cases hF : F.Nonempty
  · obtain ⟨X, hX⟩ := hF
    have hv := (mem_edges_iff X v).mp (Finset.mem_filter.mp hX).2
    have hsub : F ⊆ fixed {v.1.1, v.2.1} X := by
      intro Y hY
      have hw := (mem_edges_iff Y v).mp (Finset.mem_filter.mp hY).2
      apply (mem_fixed _ _ _).mpr
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hw.2.1.trans hv.2.1.symm
      · exact hw.2.2.trans hv.2.2.symm
    have hcard := Finset.card_le_card hsub
    simpa only [fixed_card, Finset.card_pair hv.1.ne] using hcard
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ _
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _

omit [Fintype A] in
/-- Distinct graph edges in one transversal involve at least three role labels. -/
theorem three_roles {X : Fin k → A} {v w : Coordinate k A}
    (hv : v ∈ edges X) (hw : w ∈ edges X) (hvw : v ≠ w) :
    3 ≤ ({v.1.1, v.2.1, w.1.1, w.2.1} : Finset (Fin k)).card := by
  have hv := (mem_edges_iff X v).mp hv
  have hw := (mem_edges_iff X w).mp hw
  have hextra : w.1.1 ∉ ({v.1.1, v.2.1} : Finset (Fin k)) ∨
      w.2.1 ∉ ({v.1.1, v.2.1} : Finset (Fin k)) := by
    by_contra h
    push Not at h
    have hleft := h.1
    have hright := h.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hleft hright
    have hroles : w.1.1 = v.1.1 ∧ w.2.1 = v.2.1 := by
      rcases hleft with hleft | hleft <;> rcases hright with hright | hright <;>
        simp_all
      all_goals omega
    apply hvw
    apply Prod.ext
    · apply Prod.ext hroles.1.symm
      exact hv.2.1.symm.trans (by simpa only [hroles.1] using hw.2.1)
    · apply Prod.ext hroles.2.symm
      exact hv.2.2.symm.trans (by simpa only [hroles.2] using hw.2.2)
  rcases hextra with h | h
  · have hsub : ({v.1.1, v.2.1, w.1.1} : Finset (Fin k)) ⊆ {v.1.1, v.2.1, w.1.1, w.2.1} := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at *
      tauto
    have hc := Finset.card_le_card hsub
    have hne1 : w.1.1 ≠ v.1.1 := fun heq => h (by simp [heq])
    have hne2 : w.1.1 ≠ v.2.1 := fun heq => h (by simp [heq])
    simpa [hv.1.ne, hne1, hne1.symm, hne2, hne2.symm] using hc
  · have hsub : ({v.1.1, v.2.1, w.2.1} : Finset (Fin k)) ⊆ {v.1.1, v.2.1, w.1.1, w.2.1} := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at *
      tauto
    have hc := Finset.card_le_card hsub
    have hne1 : w.2.1 ≠ v.1.1 := fun heq => h (by simp [heq])
    have hne2 : w.2.1 ≠ v.2.1 := fun heq => h (by simp [heq])
    simpa [hv.1.ne, hne1, hne1.symm, hne2, hne2.symm] using hc

/-- Two distinct graph edges fix at least three role values, giving the
required deterministic codegree bound for every actual clique hypergraph. -/
theorem codegree_le [Nonempty A] (hk : 2 ≤ k)
    (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (v w : Coordinate k A) (hvw : v ≠ w) :
    HypergraphNibble.codegree (hypergraph G) v w ≤ Fintype.card A ^ (k - 3) := by
  rw [codegree_eq hk]
  let F := (assignments G).filter (fun X => v ∈ edges X ∧ w ∈ edges X)
  by_cases hF : F.Nonempty
  · obtain ⟨X, hX⟩ := hF
    have hv := (mem_edges_iff X v).mp (Finset.mem_filter.mp hX).2.1
    have hw := (mem_edges_iff X w).mp (Finset.mem_filter.mp hX).2.2
    let S : Finset (Fin k) := {v.1.1, v.2.1, w.1.1, w.2.1}
    have hthree : 3 ≤ S.card := three_roles (Finset.mem_filter.mp hX).2.1 (Finset.mem_filter.mp hX).2.2 hvw
    have hsub : F ⊆ fixed S X := by
      intro Y hY
      have hv' := (mem_edges_iff Y v).mp (Finset.mem_filter.mp hY).2.1
      have hw' := (mem_edges_iff Y w).mp (Finset.mem_filter.mp hY).2.2
      apply (mem_fixed _ _ _).mpr
      intro i hi
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact hv'.2.1.trans hv.2.1.symm
      · exact hv'.2.2.trans hv.2.2.symm
      · exact hw'.2.1.trans hw.2.1.symm
      · exact hw'.2.2.trans hw.2.2.symm
    exact (Finset.card_le_card hsub).trans (by
      rw [fixed_card]
      exact Nat.pow_le_pow_right (by exact Fintype.card_pos) (by omega))
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ _
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _

end Erdos1017.TransversalClique
