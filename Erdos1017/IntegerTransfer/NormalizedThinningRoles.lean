module

public import Erdos1017.IntegerTransfer.ThinningBaseSelection
public import Erdos1017.IntegerTransfer.TransversalRoleHypergraph

/-!
# Normalized thinning under role permutations

Pair densities and normalized thinning probabilities transport exactly under
role permutations and are symmetric in the two endpoint roles.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- Pair densities transport exactly under role permutations. -/
theorem pairDensity_role (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin (2 + u))) (e : Fin (2 + u) × Fin (2 + u)) :
    pairDensity (G.comap (MultipartiteCounting.roleEquiv σ)) e = pairDensity G (σ e.1, σ e.2) := by
  simp only [pairDensity, GraphRelabel.edgeDensity_comap, MultipartiteCounting.part_map_roleEquiv]

omit [DecidableEq A] in
/-- Normalized thinning is symmetric in the two endpoint roles. -/
theorem normalizedProbability_symm (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (α : ℝ) (i j : Fin (2 + u)) :
    normalizedProbability G α (i, j) = normalizedProbability G α (j, i) := by
  simp only [normalizedProbability, pairDensity, eq_comm, SimpleGraph.edgeDensity_comm]

omit [DecidableEq A] in
/-- The role-coordinate equivalence pulls the original Bernoulli law back to
the normalized law of the relabelled graph. -/
theorem normalizedProbability_role (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (α : ℝ) (σ : Equiv.Perm (Fin (2 + u))) (v : Coordinate (2 + u) A) :
    partProbability (normalizedProbability G α) (roleCoordinateEquiv σ v) =
      partProbability (normalizedProbability (G.comap (MultipartiteCounting.roleEquiv σ)) α) v := by
  have heq : v.1.1 = v.2.1 ↔ σ v.1.1 = σ v.2.1 := σ.injective.eq_iff.symm
  simp only [roleCoordinateEquiv, Equiv.coe_fn_mk, roleCoordinate]
  split_ifs
  · simp only [partProbability, normalizedProbability, pairDensity_role, heq]
  · rw [partProbability, normalizedProbability_symm]
    simp only [partProbability, normalizedProbability, pairDensity_role, heq]

end Erdos1017.TransversalThinning
