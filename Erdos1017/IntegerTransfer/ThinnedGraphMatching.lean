module

public import Erdos1017.IntegerTransfer.ThinnedHypergraphMeans

/-!
# Near-perfect packing from role control of a thinned graph

The sampled edge order, the post-retention original exceptions and the aggregate
squared degree error together suffice for a near-perfect transversal clique
packing of the thinned graph (`packing_of_role_control`), with the order lower
bound supplied by the retained bases of the first two parts.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Retained bases from the initial two parts inject into the actual selected
edge set. This supplies the order lower bound needed by matching. -/
theorem retainedBases_card_le_graphEdges
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (X : Coordinate (2 + u) A → Bool) :
    (retainedBases (MultipartiteExtension.bases (t := 2) G) X).card ≤ (graphEdges (thinned G X)).card := by
  have hsub : (retainedBases (MultipartiteExtension.bases (t := 2) G) X).image (baseEdge (u := u)) ⊆
      graphEdges (thinned G X) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hx, hret⟩ := (mem_retainedBases_iff _ _ _).mp hx
    have hbase := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, by change (0 : ℕ) < 1; omega, ?_⟩
    apply (thinned_adj_iff G X (by change (0 : ℕ) < 1; omega) _ _).mpr
    exact ⟨hbase 0 1 (by decide), (baseRetained_two_iff _ _).mp hret⟩
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ baseEdge_injective] at hcard

/-- Squared error controls the number of actual selected graph edges with a
large sampled degree deviation. -/
theorem degree_deviation_count
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj]
    (α t : ℝ) (ht : 0 ≤ t) (X : Coordinate (2 + u) A → Bool) :
    t ^ 2 * (((graphEdges (thinned G X)).filter (fun v => t ≤
      |(HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v|)).card : ℝ) ≤
      ∑ v ∈ graphEdges (thinned G X),
        ((HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v) ^ 2 := by
  let U := graphEdges (thinned G X)
  let B := U.filter (fun v => t ≤ |(HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v|)
  change t ^ 2 * (B.card : ℝ) ≤ _
  calc
    _ = ∑ _ ∈ B, t ^ 2 := by simp [mul_comm]
    _ ≤ ∑ v ∈ B, ((HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v) ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      have h := (Finset.mem_filter.mp hv).2
      nlinarith [sq_abs ((HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - chartMean G α v)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- Actual sampled edge order, post-retention original exceptions and aggregate
squared degree error suffice for a near-perfect transversal clique packing. -/
theorem packing_of_role_control (u : ℕ) (hu : 0 < u) (δ₀ ρ : ℝ)
    (hδ₀ : 0 < δ₀) (hρ : 0 < ρ) :
    ∃ η D₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < D₀ ∧
      ∀ (n : ℕ), 0 < n →
        ∀ (G : SimpleGraph (Fin (2 + u) × Fin n)) [DecidableRel G.Adj]
          (α : ℝ), 0 < α →
          (∀ i j : Fin (2 + u), i < j → δ₀ ≤ pairDensity G (i, j)) →
          let D := degreeScale n u (SharedBasePattern.extensionEdges 2 u).card α
          let L : ℝ := Fintype.card (Equiv.Perm (Fin (2 + u)))
          D₀ ≤ D → (n : ℝ) ^ (u - 1) ≤ η * D →
          ∀ X : Coordinate (2 + u) (Fin n) → Bool,
            (∀ σ : Equiv.Perm (Fin (2 + u)),
              let H := G.comap (MultipartiteCounting.roleEquiv σ)
              let Y := fun v => X (roleCoordinateEquiv σ v)
              |((retainedBases (MultipartiteExtension.bases (t := 2) H) Y).card : ℝ) - α * (n : ℝ) ^ 2| < α * (n : ℝ) ^ 2 / 2 ∧
              ((retainedBases ((MultipartiteExtension.bases (t := 2) H) \ typicalBases H (η / 4)) Y).card : ℝ) <
                η * α * (n : ℝ) ^ 2 / (16 * L) ∧
              retainedSquaredError (extensions H) (partProbability (normalizedProbability H α)) Y <
                η ^ 3 * α * (n : ℝ) ^ 2 * D ^ 2 / (128 * L)) →
            ∃ T : Finset (Fin (2 + u) → Fin n), T ⊆ assignments (thinned G X) ∧
              (T : Set (Fin (2 + u) → Fin n)).PairwiseDisjoint edges ∧
                (1 - ρ) * (graphEdges (thinned G X)).card / (2 + u).choose 2 ≤ (T.card : ℝ) := by
  let C₀ := 1 + (δ₀ ^ (SharedBasePattern.extensionEdges 2 u).card)⁻¹
  have hC₀ : 1 ≤ C₀ := by
    have hnonneg : 0 ≤ (δ₀ ^ (SharedBasePattern.extensionEdges 2 u).card)⁻¹ := by positivity
    dsimp only [C₀]
    linarith
  obtain ⟨η₀, D₀, hη₀, hD₀, hmatch⟩ := exists_matching_of_squared_error (2 + u) (by omega) C₀ ρ hC₀ hρ
  let η := min η₀ 1
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hη1 : η ≤ 1 := min_le_right _ _
  refine ⟨η, D₀, hη, hη1, hD₀, ?_⟩
  intro n hn G _ α hα hd D L hD hcodeg X hcontrol
  let : NeZero n := ⟨by omega⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hDpos : 0 < D := by dsimp [D, degreeScale]; positivity
  have hL : 0 < L := by dsimp [L]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin (2 + u))))
  let U := graphEdges (thinned G X)
  let N : ℝ := U.card
  let μ := chartMean G α
  let S : ℝ := ∑ v ∈ U, ((HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - μ v) ^ 2
  let W₀ := atypicalEdges G (η / 4) X
  let W₁ := U.filter (fun v => η * D / 4 ≤ |(HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - μ v|)
  have hidentity := hcontrol (Equiv.refl (Fin (2 + u)))
  simp only [MultipartiteCounting.roleEquiv_refl, Equiv.coe_refl, SimpleGraph.comap_id,
    roleCoordinateEquiv_refl] at hidentity
  have hN : α * (n : ℝ) ^ 2 ≤ 2 * N := by
    have hcard : ((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ) ≤ N := by
      dsimp only [N, U]
      exact_mod_cast retainedBases_card_le_graphEdges G X
    have hlower := (abs_lt.mp hidentity.1).1
    nlinarith
  have hS : S ≤ η ^ 3 * α * (n : ℝ) ^ 2 * D ^ 2 / 128 := by
    have hraw := degree_squared_error_le G α X
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => (hcontrol σ).2.2.le)
    have heq : (∑ _ : Equiv.Perm (Fin (2 + u)), η ^ 3 * α * (n : ℝ) ^ 2 * D ^ 2 / (128 * L)) =
        η ^ 3 * α * (n : ℝ) ^ 2 * D ^ 2 / 128 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change L * _ = _
      field_simp
    rw [heq] at hsum
    exact hraw.trans hsum
  have hW₀ : (W₀.card : ℝ) ≤ η * α * (n : ℝ) ^ 2 / 16 := by
    have hraw := atypicalEdges_card_le G (η / 4) X
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => (hcontrol σ).2.1.le)
    have heq : (∑ _ : Equiv.Perm (Fin (2 + u)), η * α * (n : ℝ) ^ 2 / (16 * L)) = η * α * (n : ℝ) ^ 2 / 16 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change L * _ = _
      field_simp
    rw [heq] at hsum
    exact hraw.trans hsum
  have hW₁ : (W₁.card : ℝ) ≤ η * α * (n : ℝ) ^ 2 / 8 := by
    have hraw := (degree_deviation_count G α (η * D / 4) (by positivity) X).trans hS
    apply le_of_mul_le_mul_left (a := (η * D / 4) ^ 2) ?_ (by positivity)
    dsimp only [W₁, S, μ, U] at *
    nlinarith
  have hW : (((W₀ ∪ W₁) ∩ U).card : ℝ) ≤ η₀ * N := by
    have hcard : (((W₀ ∪ W₁) ∩ U).card : ℝ) ≤ W₀.card + W₁.card := by
      exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left)).trans (Finset.card_union_le W₀ W₁)
    have hscale := mul_le_mul_of_nonneg_left hN hη.le
    have hN0 : 0 ≤ N := by dsimp [N]; positivity
    nlinarith
  have hS' : S ≤ η₀ * N * D ^ 2 := by
    have hηcube : η ^ 3 ≤ η := by nlinarith [sq_nonneg η]
    have hbound := mul_le_mul_of_nonneg_right hηcube (by positivity : 0 ≤ α * (n : ℝ) ^ 2 * D ^ 2)
    have horder := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ η * D ^ 2)
    have htol := mul_le_mul_of_nonneg_right hη₀' (by positivity : 0 ≤ N * D ^ 2)
    nlinarith
  apply hmatch n hn (thinned G X) μ (W₀ ∪ W₁) D hD
  · intro v _
    simpa only [Fintype.card_fin] using chartMean_le G hα.le hδ₀ hd v
  · have hpow : 2 + u - 3 = u - 1 := by omega
    rw [hpow]
    exact hcodeg.trans (mul_le_mul_of_nonneg_right hη₀' hDpos.le)
  · intro v hv hvW
    have hv₀ : v ∉ W₀ := fun h => hvW (Finset.mem_union_left W₁ h)
    have hv₁ : v ∉ W₁ := fun h => hvW (Finset.mem_union_right W₀ h)
    have htyp : (edgeChart v).2 ∈ typicalBases (G.comap (MultipartiteCounting.roleEquiv (edgeChart v).1)) (η / 4) := by
      by_contra h
      exact hv₀ (Finset.mem_filter.mpr ⟨hv, h⟩)
    have hmean := abs_le.mp (chartMean_close G hα.le hδ₀ hd v htyp)
    have herr : |(HypergraphNibble.degree (hypergraph (thinned G X)) v : ℝ) - μ v| < η * D / 4 := by
      by_contra h
      exact hv₁ (Finset.mem_filter.mpr ⟨hv, le_of_not_gt h⟩)
    obtain ⟨hlow, hupp⟩ := abs_lt.mp herr
    simp only [Fintype.card_fin] at hmean
    change -(η / 4 * D) ≤ μ v - D ∧ μ v - D ≤ η / 4 * D at hmean
    have htol := mul_le_mul_of_nonneg_right hη₀' hDpos.le
    constructor <;> nlinarith only [hmean.1, hmean.2, hlow, hupp, htol]
  · exact hW
  · exact hS'

end Erdos1017.TransversalClique
