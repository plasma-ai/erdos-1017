module

public import Erdos1017.IntegerTransfer.TransversalEdgeCharts
public import Erdos1017.IntegerTransfer.ThinnedHypergraphMeans
public import Erdos1017.IntegerTransfer.MultipartiteEdgeSums

/-!
# Edge counts of the thinned graph by role pair

The sampled edge count of a role pair is exactly the retained two-role base
count in its chart (`pairEdgeCount_thinned`), so simultaneous retained pair
control bounds the total sampled graph order
(`graphEdges_card_le_of_role_control`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning MultipartiteAllocation

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- A sampled role pair is exactly the retained two-role base count in its chart. -/
theorem pairEdgeCount_thinned (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (X : Coordinate (2 + u) A → Bool) (i j : Fin (2 + u)) (hij : i < j) :
    pairEdgeCount (thinned G X) i j =
      (retainedBases (MultipartiteExtension.bases (t := 2)
        (G.comap (MultipartiteCounting.roleEquiv (pairRoleEquiv i j))))
          (fun v => X (roleCoordinateEquiv (pairRoleEquiv i j) v))).card := by
  symm
  let σ := pairRoleEquiv i j
  have hmem (x : Fin 2 → A) :
      x ∈ retainedBases (MultipartiteExtension.bases (t := 2)
        (G.comap (MultipartiteCounting.roleEquiv σ))) (fun v => X (roleCoordinateEquiv σ v)) ↔
        (thinned G X).Adj (i, x 0) (j, x 1) := by
    rw [mem_retainedBases_iff, baseRetained_two_iff, thinned_adj_iff G X hij]
    have hedge : roleCoordinateEquiv σ (baseEdge x) = ((i, x 0), (j, x 1)) := by
      rw [show roleCoordinateEquiv σ (baseEdge x) = roleCoordinate σ (baseEdge x) from rfl,
        roleCoordinate_of_lt _ _ (by change (0 : ℕ) < 1; omega)]
      simp only [σ, baseEdge, pairRoleEquiv_first _ _ hij.ne, pairRoleEquiv_second, hij, ite_true]
    rw [hedge]
    apply and_congr ?_ Iff.rfl
    simp only [MultipartiteExtension.bases, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h := h 0 1 (by decide)
      simpa only [SimpleGraph.comap_adj, MultipartiteCounting.roleEquiv, Equiv.prodCongr_apply,
        Equiv.refl_apply, Prod.map_apply, σ, pairRoleEquiv_first _ _ hij.ne, pairRoleEquiv_second] using h
    · intro h a b hab
      have hAdj : (G.comap (MultipartiteCounting.roleEquiv σ)).Adj
          (Fin.castAdd u 0, x 0) (Fin.castAdd u 1, x 1) := by
        simpa only [SimpleGraph.comap_adj, MultipartiteCounting.roleEquiv, Equiv.prodCongr_apply,
          Equiv.refl_apply, Prod.map_apply, σ, pairRoleEquiv_first _ _ hij.ne, pairRoleEquiv_second] using h
      fin_cases a <;> fin_cases b
      all_goals first | exact hAdj | (simp only [Fin.lt_def] at hab; omega)
  apply Finset.card_bij (fun x _ => (x 0, x 1))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem x).mp hx⟩
  · intro x _ y _ hxy
    funext a
    fin_cases a
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  · intro p hp
    let x : Fin 2 → A := ![p.1, p.2]
    refine ⟨x, (hmem x).mpr ?_, ?_⟩
    · exact (Finset.mem_filter.mp hp).2
    · rfl

/-- Simultaneous retained pair control bounds the actual total sampled graph order. -/
theorem graphEdges_card_le_of_role_control
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (X : Coordinate (2 + u) A → Bool) (α ρ : ℝ)
    (h : ∀ σ : Equiv.Perm (Fin (2 + u)),
      |((retainedBases (MultipartiteExtension.bases (t := 2) (G.comap (MultipartiteCounting.roleEquiv σ)))
        (fun v => X (roleCoordinateEquiv σ v))).card : ℝ) - α * (Fintype.card A : ℝ) ^ 2| <
          ρ * α * (Fintype.card A : ℝ) ^ 2) :
    ((graphEdges (thinned G X)).card : ℝ) ≤
      (2 + u).choose 2 * ((1 + ρ) * α * (Fintype.card A : ℝ) ^ 2) := by
  apply graphEdges_card_le
  intro i j hij
  rw [pairEdgeCount_thinned G X i j hij]
  have hupper := (abs_lt.mp (h (pairRoleEquiv i j))).2
  linarith

end Erdos1017.TransversalClique
