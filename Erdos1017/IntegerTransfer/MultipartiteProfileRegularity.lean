module

public import Erdos1017.IntegerTransfer.MultipartiteProfileGraphs

/-!
# Regularity and density bounds of profile graphs

A profile with nonzero clique mass uses only nonempty part pairs, so every
required pair of its induced `profileGraph` is regular and dense, and its mass
is at most `n²`, which gives the normalized thinning probability bounds on
`allocationDensity` with `C` fixed before the regularity partition.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteAllocation

variable {ℓ C : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Increasing enumeration of a profile with at least two roles. -/
def profileRoleEmbedding (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card) :
    Fin (2 + (K.card - 2)) ↪o Fin ℓ := K.orderEmbOfFin (by omega)

/-- Every enumerated role belongs to the profile. -/
theorem profileRoleEmbedding_mem (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card)
    (i : Fin (2 + (K.card - 2))) : profileRoleEmbedding K hK i ∈ K :=
  K.orderEmbOfFin_mem _ i

/-- The actual graph induced on all vertices of the selected profile parts. -/
def profileGraph (G : SimpleGraph (Fin ℓ × A)) (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card) :
    SimpleGraph (Fin (2 + (K.card - 2)) × A) :=
  G.comap (MultipartiteCounting.partVertexEmbedding (profileRoleEmbedding K hK).toEmbedding)

instance (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card) : DecidableRel (profileGraph G K hK).Adj :=
  inferInstanceAs (DecidableRel (G.comap _).Adj)

omit [DecidableEq A] in
/-- A profile with nonzero actual clique mass uses only nonempty part pairs,
so the cleaned graph's regular branch applies at every required pair. -/
theorem profileGraph_regular_density [Nonempty A]
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (w : Finset (Fin ℓ × A) → ℝ)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (ε δ : ℝ)
    (hclean : ∀ i j : Fin ℓ, i < j →
      (∀ a b : A, ¬G.Adj (i, a) (j, b)) ∨
        (G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
          δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j)))
    (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card) (hmass : typeMass w K ≠ 0)
    (i j : Fin (2 + (K.card - 2))) (hij : i < j) :
    (profileGraph G K hK).IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
      δ ≤ TransversalThinning.pairDensity (t := 2) (u := K.card - 2) (profileGraph G K hK) (i, j) := by
  let φ := profileRoleEmbedding K hK
  have hlt := φ.strictMono hij
  have hpos := typeMass_pair_positive G w hsupport K hmass (φ i) (φ j)
    (profileRoleEmbedding_mem K hK i) (profileRoleEmbedding_mem K hK j) hlt.ne
  rcases hclean (φ i) (φ j) hlt with hempty | hregular
  · have hzero : pairEdgeCount G (φ i) (φ j) = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hempty p.1 p.2 (Finset.mem_filter.mp hp).2
    omega
  · constructor
    · exact MultipartiteCounting.part_regular_embedding G φ.toEmbedding i j ε hregular.1
    · change δ ≤ ((G.comap (MultipartiteCounting.partVertexEmbedding φ.toEmbedding)).edgeDensity
        (MultipartiteCounting.part i) (MultipartiteCounting.part j) : ℝ)
      rw [MultipartiteCounting.part_density_embedding]
      exact hregular.2

omit [DecidableEq A] in
/-- Any one actual part pair has at most n² graph edges. -/
theorem pairEdgeCount_le (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj] (i j : Fin ℓ) :
    pairEdgeCount G i j ≤ Fintype.card A ^ 2 := by
  have h := Finset.card_le_card (Finset.filter_subset (fun p : A × A => G.Adj (i, p.1) (j, p.2)) Finset.univ)
  simpa only [pairEdgeCount, Finset.card_univ, Fintype.card_prod, pow_two] using h

/-- A profile mass is at most n². Splitting into C layers can therefore force
its normalized density parameter below a fixed density floor. -/
theorem typeMass_le_part_square
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card) : typeMass w K ≤ (Fintype.card A : ℝ) ^ 2 := by
  obtain ⟨i, hi, j, hj, hij⟩ := (Finset.one_lt_card (s := K)).mp (by omega)
  have h := typeMass_le_pairEdgeCount G hparts w hw hsupport hbalance K i j hij hi hj
  have hcard : (pairEdgeCount G i j : ℝ) ≤ (Fintype.card A : ℝ) ^ 2 := by exact_mod_cast pairEdgeCount_le G i j
  exact h.trans hcard

/-- The actual fractional allocation parameter satisfies the normalized
thinning probability bounds, with C fixed before the regularity partition. -/
theorem allocationDensity_bounds [Nonempty A]
    (G : SimpleGraph (Fin ℓ × A)) [DecidableRel G.Adj]
    (hparts : ∀ i (a b : A), ¬G.Adj (i, a) (i, b))
    (w : Finset (Fin ℓ × A) → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hsupport : ∀ S, w S ≠ 0 → G.IsClique (S : Set (Fin ℓ × A)))
    (hbalance : ∀ v z, G.Adj v z → pairLoad w v z = 1)
    (δ : ℝ) (C : ℕ) (hC : 0 < C) (hscale : 1 ≤ (C : ℝ) * δ)
    (K : Finset (Fin ℓ)) (hK : 2 ≤ K.card) (hmass : 0 < typeMass w K) :
    0 < allocationDensity (Fintype.card A) C (typeMass w K) ∧
      allocationDensity (Fintype.card A) C (typeMass w K) ≤ δ := by
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  constructor
  · exact div_pos hmass (mul_pos hCp (sq_pos_of_pos hn))
  · apply (div_le_iff₀ (mul_pos hCp (sq_pos_of_pos hn))).mpr
    have hmass := typeMass_le_part_square G hparts w hw hsupport hbalance K hK
    have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Fintype.card A : ℝ))
    nlinarith only [hmass, hmul]

end Erdos1017.MultipartiteAllocation
