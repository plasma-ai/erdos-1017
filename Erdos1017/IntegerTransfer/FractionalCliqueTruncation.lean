module

public import Erdos1017.IntegerTransfer.CliqueTruncation
public import Erdos1017.LowerBound.WeightedGraphRealization

/-!
# Truncating fractional partitions to bounded cliques

This module replaces each large clique by all of its `r`-vertex subcliques with
exact pair loads (`truncationKernel`), giving a bounded-clique fractional
partition with controlled additive cost loss, where the clique-size cutoff is
fixed independently of the graph order
(`exists_uniform_bounded_clique_partition`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n : ℕ}

theorem clique_adjacency_charge (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : G.IsClique (S : Set (Fin n))) :
    WeightedGraph.charge (WeightedGraph.adjacencyMatrix G) S = (S.card.choose 2 : ℝ) := by
  classical
  rw [WeightedGraph.charge_eq_sum]
  have hinner (i : Fin n) (hi : i ∈ S) :
      (∑ j ∈ S, WeightedGraph.adjacencyMatrix G i j) = (S.card : ℝ) - 1 := by
    calc
      _ = ∑ j ∈ S, (1 - if j = i then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : j = i
        · subst j
          simp [WeightedGraph.adjacencyMatrix]
        · simp [WeightedGraph.adjacencyMatrix, hS hi hj (Ne.symm hij), hij]
      _ = (S.card : ℝ) - 1 := by simp [Finset.sum_sub_distrib, hi]
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_choose_two]

theorem subset_pair_mass (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) :
    (∑ S, w S * (S.card.choose 2 : ℝ)) = G.edgeSet.ncard := by
  have hleft : (∑ S, w S * (S.card.choose 2 : ℝ)) =
      ∑ S, w S * WeightedGraph.charge (WeightedGraph.adjacencyMatrix G) S := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hz : w S = 0
    · simp [hz]
    · rw [clique_adjacency_charge G S (hw.2.1 S hz).2]
  rw [hleft, WeightedGraph.weighted_charge_identity]
  have hterm (i j : Fin n) : WeightedGraph.adjacencyMatrix G i j * pairLoad w i j =
      WeightedGraph.adjacencyMatrix G i j := by
    by_cases hij : G.Adj i j
    · rw [hw.2.2 i j hij, mul_one]
    · simp [WeightedGraph.adjacencyMatrix, hij]
  simp_rw [hterm]
  have h := WeightedGraph.adjacency_objective G
  simpa only [WeightedGraph.objective, mul_one] using h

/-- Each large clique is replaced by all of its `r`-vertex subcliques with exact pair loads. -/
def truncationKernel (r : ℕ) (S T : Finset (Fin n)) : ℝ :=
  if S.card ≤ r then (if T = S then 1 else 0)
  else if T ∈ S.powersetCard r then ((S.card - 2).choose (r - 2) : ℝ)⁻¹ else 0

theorem truncationKernel_nonneg (r : ℕ) (S T : Finset (Fin n)) : 0 ≤ truncationKernel r S T := by
  unfold truncationKernel
  split_ifs <;> positivity

theorem truncationKernel_supported (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n)))
    (T : Finset (Fin n)) (hT : truncationKernel r S T ≠ 0) :
    2 ≤ T.card ∧ G.IsClique (T : Set (Fin n)) ∧ T.card ≤ r := by
  by_cases hs : S.card ≤ r
  · have heq : T = S := by
      by_contra hne
      exact hT (by simp [truncationKernel, hs, hne])
    subst T
    exact ⟨hS.1, hS.2, hs⟩
  · have hmem : T ∈ S.powersetCard r := by
      by_contra hnot
      exact hT (by simp [truncationKernel, hs, hnot])
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hmem
    exact ⟨hcard ▸ hr, hS.2.subset hsub, hcard.le⟩

theorem truncationKernel_pairLoad (r : ℕ) (hr : 2 ≤ r) (S : Finset (Fin n))
    (u v : Fin n) (huv : u ≠ v) :
    pairLoad (truncationKernel r S) u v = if u ∈ S ∧ v ∈ S then 1 else 0 := by
  classical
  by_cases hs : S.card ≤ r
  · have heq : truncationKernel r S = (fun T => if T = S then 1 else 0) := by
      funext T
      simp only [truncationKernel, ite_eq_left hs]
    rw [heq, pairLoad_single]
  · have hrs : r ≤ S.card := (Nat.le_of_lt (Nat.lt_of_not_ge hs))
    unfold pairLoad
    simp only [truncationKernel, ite_eq_right hs]
    have hsum : (∑ T : Finset (Fin n), if u ∈ T ∧ v ∈ T then
          (if T ∈ S.powersetCard r then ((S.card - 2).choose (r - 2) : ℝ)⁻¹ else 0) else 0) =
        ∑ T ∈ S.powersetCard r,
          if ({u, v} : Finset (Fin n)) ⊆ T then ((S.card - 2).choose (r - 2) : ℝ)⁻¹ else 0 := by
      have hterm (T : Finset (Fin n)) :
          (if u ∈ T ∧ v ∈ T then
            (if T ∈ S.powersetCard r then ((S.card - 2).choose (r - 2) : ℝ)⁻¹ else 0) else 0) =
          if T ∈ S.powersetCard r then
            (if u ∈ T ∧ v ∈ T then ((S.card - 2).choose (r - 2) : ℝ)⁻¹ else 0) else 0 := by
        split_ifs <;> simp_all
      simp_rw [hterm]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [hsum]
    by_cases hpair : u ∈ S ∧ v ∈ S
    · rw [ite_eq_left hpair]
      exact CliqueTruncation.uniform_pair_load S {u, v} (Finset.card_pair huv)
        (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hpair) r hr hrs
    · rw [ite_eq_right hpair]
      apply Finset.sum_eq_zero
      intro T hT
      have hsub := (Finset.mem_powersetCard.mp hT).1
      have hnot : ¬({u, v} : Finset (Fin n)) ⊆ T := by
        intro h
        exact hpair ⟨hsub (h (by simp)), hsub (h (by simp))⟩
      simp [hnot]

theorem truncationKernel_cost (r : ℕ) (hr : 2 ≤ r) (S : Finset (Fin n)) :
    (∑ T, truncationKernel r S T) ≤ 1 + (S.card.choose 2 : ℝ) / (r.choose 2 : ℝ) := by
  classical
  by_cases hs : S.card ≤ r
  · simp only [truncationKernel, ite_eq_left hs, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hrs : r ≤ S.card := Nat.le_of_lt (Nat.lt_of_not_ge hs)
    have heq : (∑ T, truncationKernel r S T) =
        ∑ _T ∈ S.powersetCard r, ((S.card - 2).choose (r - 2) : ℝ)⁻¹ := by
      simp only [truncationKernel, ite_eq_right hs, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [heq, CliqueTruncation.uniform_cost S r hr hrs]
    linarith

def truncatedWeights (r : ℕ) (w : Finset (Fin n) → ℝ) (T : Finset (Fin n)) : ℝ :=
  ∑ S, w S * truncationKernel r S T

theorem truncatedWeights_supported (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r)
    (w : Finset (Fin n) → ℝ) (hw : SubsetFeasible G w)
    (T : Finset (Fin n)) (hT : truncatedWeights r w T ≠ 0) :
    2 ≤ T.card ∧ G.IsClique (T : Set (Fin n)) ∧ T.card ≤ r := by
  obtain ⟨S, _, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  have hparts := mul_ne_zero_iff.mp hS
  exact truncationKernel_supported G r hr S (hw.2.1 S hparts.1) T hparts.2

theorem truncatedWeights_feasible (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r)
    (w : Finset (Fin n) → ℝ) (hw : SubsetFeasible G w) : SubsetFeasible G (truncatedWeights r w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (hw.1 S) (truncationKernel_nonneg r S T))
  · intro T hT
    have h := truncatedWeights_supported G r hr w hw T hT
    exact ⟨h.1, h.2.1⟩
  · intro a b hab
    unfold truncatedWeights
    rw [pairLoad_sum_mul]
    simp_rw [truncationKernel_pairLoad r hr _ a b hab.ne]
    simpa [pairLoad, mul_ite] using hw.2.2 a b hab

theorem truncatedWeights_cost (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r)
    (w : Finset (Fin n) → ℝ) (hw : SubsetFeasible G w) :
    (∑ T, truncatedWeights r w T) ≤ (∑ S, w S) + (G.edgeSet.ncard : ℝ) / (r.choose 2 : ℝ) := by
  unfold truncatedWeights
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    (∑ S, w S * ∑ T, truncationKernel r S T) ≤
        ∑ S, w S * (1 + (S.card.choose 2 : ℝ) / (r.choose 2 : ℝ)) :=
      Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (truncationKernel_cost r hr S) (hw.1 S))
    _ = _ := by
      simp only [mul_add, mul_one, mul_div, Finset.sum_add_distrib, ← Finset.sum_div,
        subset_pair_mass G w hw]

/-- An actual bounded-clique fractional partition with controlled additive cost loss. -/
theorem exists_bounded_clique_partition (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r) :
    ∃ w : Finset (Fin n) → ℝ, SubsetFeasible G w ∧
      (∀ S, w S ≠ 0 → S.card ≤ r) ∧
      (∑ S, w S) ≤ value G + (G.edgeSet.ncard : ℝ) / (r.choose 2 : ℝ) := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  let v := extendWeights G w
  have hv := extendWeights_feasible G w hw
  refine ⟨truncatedWeights r v, truncatedWeights_feasible G r hr v hv, ?_, ?_⟩
  · intro S hS
    exact (truncatedWeights_supported G r hr v hv S hS).2.2
  · have h := truncatedWeights_cost G r hr v hv
    have hcost : (∑ S, v S) = value G := by
      rw [value_eq_optimal G w hw hmin]
      simpa [v, FinitePrimal.cost] using extendWeights_sum G w (fun _ => 1)
    rwa [hcost] at h

/-- The clique-size cutoff can be fixed independently of the graph order. -/
theorem exists_uniform_bounded_clique_partition (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 2 ≤ r ∧ ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ∃ w : Finset (Fin n) → ℝ, SubsetFeasible G w ∧
        (∀ S, w S ≠ 0 → S.card ≤ r) ∧ (∑ S, w S) ≤ value G + ε * (n : ℝ) ^ 2 := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε + 2)
  have hinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hrreal : (2 : ℝ) ≤ r := by linarith
  have hrnat : 2 ≤ r := by exact_mod_cast hrreal
  have hchoose : 1 / ε < (r.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hmul := mul_nonneg (sub_nonneg.mpr hrreal) (show 0 ≤ (r : ℝ) - 1 by linarith)
    nlinarith
  have hden : 0 < (r.choose 2 : ℝ) := hinv.trans hchoose
  have hinvbound : (r.choose 2 : ℝ)⁻¹ ≤ ε := by
    have hprod := (div_lt_iff₀ hε).mp hchoose
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  refine ⟨r, hrnat, ?_⟩
  intro n G
  obtain ⟨w, hw, hsupport, hcost⟩ := exists_bounded_clique_partition G r hrnat
  refine ⟨w, hw, hsupport, hcost.trans ?_⟩
  have hcard : (G.edgeSet.ncard : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (edge_count_le_choose G).trans (Nat.choose_le_pow n 2)
  have hbound : (G.edgeSet.ncard : ℝ) / (r.choose 2 : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (n : ℝ) ^ 2 * (r.choose 2 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hden.le)
      _ ≤ (n : ℝ) ^ 2 * ε := mul_le_mul_of_nonneg_left hinvbound (sq_nonneg _)
      _ = _ := mul_comm _ _
  linarith

end Erdos1017.FractionalGraph
