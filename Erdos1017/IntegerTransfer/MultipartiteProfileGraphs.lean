module

public import Erdos1017.IntegerTransfer.MultipartiteAllocationLaw
public import Erdos1017.IntegerTransfer.GraphEmbeddingRegularity
public import Erdos1017.IntegerTransfer.NormalizedThinningRoles

/-!
# Profile graphs embedded in ambient parts

This module embeds the graph-edge coordinates of a profile in its selected
ambient parts, identifies part-pair densities with edge cardinalities over `n²`,
defines the normalized density `allocationDensity` of an allocation layer, and
shows that the categorical law has the normalized-thinning marginal on every
coordinate of the embedded profile graph.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

open scoped BigOperators

variable {ℓ k C : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- A pair of within-part coordinates identifies one ordered physical interedge. -/
def pairCoordinateEmbedding (i j : Fin ℓ) : (A × A) ↪ ((Fin ℓ × A) × (Fin ℓ × A)) where
  toFun p := ((i, p.1), (j, p.2))
  inj' := by intro p q h; exact Prod.ext (congrArg (fun v => v.1.2) h) (congrArg (fun v => v.2.2) h)

omit [DecidableEq A] in
/-- Actual interedges between two parts are exactly the corresponding endpoint pairs. -/
theorem pairEdgeCount_interedges (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (i j : Fin ℓ) :
    pairEdgeCount G i j = (G.interedges (MultipartiteCounting.part i) (MultipartiteCounting.part j)).card := by
  have heq : (Finset.univ.filter (fun p : A × A => G.Adj (i, p.1) (j, p.2))).map
      (pairCoordinateEmbedding i j) = G.interedges (MultipartiteCounting.part i) (MultipartiteCounting.part j) := by
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_interedges_iff]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact ⟨(TransversalThinning.mem_part_iff _ _).mpr rfl,
        (TransversalThinning.mem_part_iff _ _).mpr rfl, hab⟩
    · rintro ⟨hleft, hright, hadj⟩
      have hleft := (TransversalThinning.mem_part_iff _ _).mp hleft
      have hright := (TransversalThinning.mem_part_iff _ _).mp hright
      refine ⟨(v.1.2, v.2.2), ?_, Prod.ext (Prod.ext hleft.symm rfl) (Prod.ext hright.symm rfl)⟩
      convert hadj using 1
      · exact Prod.ext hleft.symm rfl
      · exact Prod.ext hright.symm rfl
  have h := congrArg Finset.card heq
  simpa only [Finset.card_map, pairEdgeCount] using h

omit [DecidableEq A] in
/-- The ambient part-pair density is exactly its actual edge cardinality divided by n². -/
theorem pair_density_eq [Nonempty A] (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (i j : Fin ℓ) :
    (G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j) : ℝ) =
      (pairEdgeCount G i j : ℝ) / (Fintype.card A : ℝ) ^ 2 := by
  rw [pairEdgeCount_interedges]
  simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, MultipartiteCounting.part, Finset.card_map,
    Finset.card_univ, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, SimpleGraph.interedges, pow_two]

omit [DecidableEq A] in
/-- A positive actual profile mass forces a graph edge between each two used parts. -/
theorem typeMass_pair_positive (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (K : Finset (Fin ℓ)) (hK : typeMass w K ≠ 0)
    (i j : Fin ℓ) (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) : 0 < pairEdgeCount G i j := by
  obtain ⟨S, hprofile, hw⟩ := typeMass_witness w K hK
  rw [← hprofile] at hi hj
  obtain ⟨⟨i', a⟩, ha, hia⟩ := Finset.mem_image.mp hi
  obtain ⟨⟨j', b⟩, hb, hjb⟩ := Finset.mem_image.mp hj
  change i' = i at hia
  change j' = j at hjb
  subst i'
  subst j'
  have hadj := hsupport S hw ha hb (fun h => hij (congrArg Prod.fst h))
  exact Finset.card_pos.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩

/-- Embed all local graph-edge coordinates in their selected ambient parts. -/
def profileCoordinateEmbedding (φ : Fin k ↪ Fin ℓ) :
    TransversalThinning.Coordinate k A ↪ TransversalThinning.Coordinate ℓ A :=
  (MultipartiteCounting.partVertexEmbedding φ).prodMap (MultipartiteCounting.partVertexEmbedding φ)

/-- The normalized density parameter of one allocation layer. -/
def allocationDensity (n C : ℕ) (mass : ℝ) : ℝ := mass / ((C : ℝ) * (n : ℝ) ^ 2)

omit [DecidableEq A] in
/-- The actual categorical law has exactly the normalized-thinning marginal
on every coordinate of an embedded profile graph. -/
theorem allocationProbability_profile [Nonempty A]
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (mass : Finset (Fin ℓ) → ℝ) (C : ℕ) (hC : 0 < C)
    (K : Finset (Fin ℓ)) (c : Fin C) (φ : Fin k ↪ Fin ℓ)
    (hφ : ∀ i, φ i ∈ K)
    (hpair : ∀ i j : Fin k, i ≠ j → 0 < pairEdgeCount G (φ i) (φ j))
    (v : TransversalThinning.Coordinate k A) :
    allocationProbability G mass C (profileCoordinateEmbedding φ v) (some (K, c)) =
      TransversalThinning.partProbability (t := k) (u := 0)
        (TransversalThinning.normalizedProbability (t := k) (u := 0) (G.comap (MultipartiteCounting.partVertexEmbedding φ))
          (allocationDensity (Fintype.card A) C (mass K))) v := by
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  by_cases hv : v.1.1 = v.2.1
  · have hsame : ¬ActivePair G (profileCoordinateEmbedding φ v) := by
      intro h
      exact h.1 (congrArg φ hv)
    simp only [allocationProbability, hsame, false_and, ite_false, TransversalThinning.partProbability,
      TransversalThinning.normalizedProbability, ite_eq_left hv]
  · have hpositive := hpair v.1.1 v.2.1 hv
    have hactive : ActivePair G (profileCoordinateEmbedding φ v) := ⟨φ.injective.ne hv, hpositive⟩
    have hcount : (0 : ℝ) < pairEdgeCount G (φ v.1.1) (φ v.2.1) := by exact_mod_cast hpositive
    have hleft : ((profileCoordinateEmbedding φ) v).1.1 ∈ K := hφ v.1.1
    have hright : ((profileCoordinateEmbedding φ) v).2.1 ∈ K := hφ v.2.1
    simp only [allocationProbability, hactive, hleft, hright, and_self, ite_true, TransversalThinning.partProbability,
      TransversalThinning.normalizedProbability, ite_eq_right hv, TransversalThinning.pairDensity,
      MultipartiteCounting.part_density_embedding, pair_density_eq, allocationDensity]
    change mass K / ((C : ℝ) * pairEdgeCount G (φ v.1.1) (φ v.2.1)) =
      (mass K / ((C : ℝ) * (Fintype.card A : ℝ) ^ 2)) /
        ((pairEdgeCount G (φ v.1.1) (φ v.2.1) : ℝ) / (Fintype.card A : ℝ) ^ 2)
    field_simp

end Erdos1017.MultipartiteAllocation
