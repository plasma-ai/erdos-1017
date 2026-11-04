module

public import Erdos1017.FractionalLimit.FractionalGraphCounts
public import Erdos1017.FractionalLimit.FractionalGraphEmbedding
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Fractional extremum at a prescribed edge count

This module defines `extremal`, the fractional extremum over graphs with an
exact edge count (zero for impossible counts), and proves that it is
nonnegative, attained over a finite set, and satisfies the asymmetric edit
bounds (`extremal_edit_bounds`, `extremal_abs_sub_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n : ℕ}

/-- The exact-edge-count fractional extremum, with value zero for impossible counts. -/
def extremal (n k : ℕ) : ℝ :=
  sSup (insert 0 {c | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ value G = c})

theorem extremal_set_finite (n k : ℕ) :
    (insert (0 : ℝ) {c | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ value G = c}).Finite := by
  apply Set.Finite.insert
  apply (Set.finite_range (fun G : SimpleGraph (Fin n) => value G)).subset
  rintro c ⟨G, _, rfl⟩
  exact Set.mem_range_self G

theorem extremal_nonneg (n k : ℕ) : 0 ≤ extremal n k :=
  le_csSup (extremal_set_finite n k).bddAbove (Set.mem_insert 0 _)

theorem value_le_extremal (G : SimpleGraph (Fin n)) : value G ≤ extremal n G.edgeSet.ncard :=
  le_csSup (extremal_set_finite n _).bddAbove (Set.mem_insert_of_mem _ ⟨G, rfl, rfl⟩)

theorem value_le_edge_count (G : SimpleGraph (Fin n)) : value G ≤ G.edgeSet.ncard := by
  classical
  obtain ⟨P, hP, hc⟩ := G.exists_isCliqueEdgePartition_card_eq
  have hmin := value_le_cliquePartitionNumber G
  have hcp : Erdos1017.cliquePartitionNumber G ≤ G.edgeFinset.card :=
    (Erdos1017.cliquePartitionNumber_le_iff G).mpr ⟨P, hP, hc.le⟩
  have he : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he]
  exact hmin.trans (by exact_mod_cast hcp)

theorem extremal_le (n k : ℕ) : extremal n k ≤ k := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro c (rfl | ⟨G, hG, rfl⟩)
  · exact Nat.cast_nonneg _
  · simpa [hG] using value_le_edge_count G

theorem extremal_attained_of_exists (k : ℕ)
    (hex : ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ value G = extremal n k := by
  have hmem := (Set.insert_nonempty (0 : ℝ)
    {c | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ value G = c}).csSup_mem
    (extremal_set_finite n k)
  rcases hmem with hzero | hG
  · obtain ⟨G, hG⟩ := hex
    refine ⟨G, hG, le_antisymm ?_ ?_⟩
    · simpa [hG] using value_le_extremal G
    · change sSup _ ≤ value G
      rw [hzero]
      exact value_nonneg G
  · exact hG

theorem edgeSet_from_subset (G : SimpleGraph (Fin n)) (S : Finset (Sym2 (Fin n)))
    (hS : (S : Set (Sym2 (Fin n))) ⊆ G.edgeSet) :
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin n)))).edgeSet = (S : Set (Sym2 (Fin n))) := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun h => h.1
  · intro he
    exact ⟨he, G.edgeSet_subset_compl_diagSet (hS he)⟩

theorem exists_subgraph_edge_count (G : SimpleGraph (Fin n)) (k : ℕ)
    (hk : k ≤ G.edgeSet.ncard) :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.edgeSet.ncard = k := by
  classical
  have hcard : (finiteEdges G).card = G.edgeSet.ncard := by
    unfold finiteEdges
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  obtain ⟨S, hS, hSk⟩ := Finset.exists_subset_card_eq (hcard ▸ hk)
  have hsub : (S : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
    intro e he
    have := hS he
    simpa [finiteEdges] using this
  refine ⟨SimpleGraph.fromEdgeSet S, ?_, ?_⟩
  · rw [← SimpleGraph.fromEdgeSet_edgeSet G]
    exact SimpleGraph.fromEdgeSet_mono hsub
  · rw [edgeSet_from_subset G S hsub, Set.ncard_coe_finset, hSk]

theorem exists_graph_edge_count (n k : ℕ) (hk : k ≤ n.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k := by
  classical
  have htop : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  obtain ⟨G, _, hG⟩ := exists_subgraph_edge_count ⊤ k (htop ▸ hk)
  exact ⟨G, hG⟩

theorem extremal_attained (n k : ℕ) (hk : k ≤ n.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = k ∧ value G = extremal n k :=
  extremal_attained_of_exists k (exists_graph_edge_count n k hk)

theorem finiteEdges_card (G : SimpleGraph (Fin n)) : (finiteEdges G).card = G.edgeSet.ncard := by
  classical
  unfold finiteEdges
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

theorem finiteEdges_mono {G H : SimpleGraph (Fin n)} (h : G ≤ H) :
    finiteEdges G ⊆ finiteEdges H := by
  classical
  exact SimpleGraph.edgeFinset_mono h

theorem exists_supergraph_edge_count (G : SimpleGraph (Fin n)) (k : ℕ)
    (hG : G.edgeSet.ncard ≤ k) (hk : k ≤ n.choose 2) :
    ∃ H : SimpleGraph (Fin n), G ≤ H ∧ H.edgeSet.ncard = k := by
  classical
  have htop : (finiteEdges (⊤ : SimpleGraph (Fin n))).card = n.choose 2 := by
    have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    simp only [Fintype.card_fin] at h
    convert h using 1
    congr 1
    ext e
    simp [finiteEdges]
  obtain ⟨S, hGS, hStop, hSk⟩ := Finset.exists_subsuperset_card_eq
    (finiteEdges_mono (show G ≤ ⊤ from le_top)) ((finiteEdges_card G).symm ▸ hG) (htop ▸ hk)
  have hsub : (S : Set (Sym2 (Fin n))) ⊆ (⊤ : SimpleGraph (Fin n)).edgeSet := by
    intro e he
    have := hStop he
    simpa [finiteEdges] using this
  refine ⟨SimpleGraph.fromEdgeSet S, ?_, ?_⟩
  · rw [← SimpleGraph.fromEdgeSet_edgeSet G]
    apply SimpleGraph.fromEdgeSet_mono
    intro e he
    apply hGS
    simpa [finiteEdges] using he
  · rw [edgeSet_from_subset ⊤ S hsub, Set.ncard_coe_finset, hSk]

theorem value_bounds_of_subgraph (G H : SimpleGraph (Fin n)) (hGH : G ≤ H) :
    value H ≤ value G + (H.edgeSet.ncard : ℝ) - G.edgeSet.ncard ∧
      value G ≤ value H + 3 * ((H.edgeSet.ncard : ℝ) - G.edgeSet.ncard) := by
  have hsub := finiteEdges_mono hGH
  have hcard := Finset.card_le_card hsub
  have hdiff : (finiteEdges G \ finiteEdges H) = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
  have hcount : ((finiteEdges H \ finiteEdges G).card : ℝ) =
      (H.edgeSet.ncard : ℝ) - G.edgeSet.ncard := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub hcard, finiteEdges_card, finiteEdges_card]
  have h₁ := value_le_edit_cost G H
  have h₂ := value_le_edit_cost H G
  rw [hdiff, Finset.card_empty, Nat.cast_zero, hcount] at h₁ h₂
  constructor <;> linarith

/-- The exact prescribed-edge-count extremum has the asymmetric edit bounds. -/
theorem extremal_edit_bounds (n k₁ k₂ : ℕ) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ n.choose 2) :
    extremal n k₂ ≤ extremal n k₁ + (k₂ : ℝ) - k₁ ∧
      extremal n k₁ ≤ extremal n k₂ + 3 * ((k₂ : ℝ) - k₁) := by
  constructor
  · obtain ⟨H, hH, hvH⟩ := extremal_attained n k₂ h₂
    obtain ⟨G, hGH, hG⟩ := exists_subgraph_edge_count H k₁ (hH ▸ h₁₂)
    have hbound := (value_bounds_of_subgraph G H hGH).1
    have hmax := value_le_extremal G
    rw [hG] at hmax hbound
    rw [hH, hvH] at hbound
    linarith
  · obtain ⟨G, hG, hvG⟩ := extremal_attained n k₁ (h₁₂.trans h₂)
    obtain ⟨H, hGH, hH⟩ := exists_supergraph_edge_count G k₂ (hG ▸ h₁₂) h₂
    have hbound := (value_bounds_of_subgraph G H hGH).2
    have hmax := value_le_extremal H
    rw [hH] at hmax hbound
    rw [hG, hvG] at hbound
    linarith

theorem extremal_abs_sub_le (n k l : ℕ) (hk : k ≤ n.choose 2) (hl : l ≤ n.choose 2) :
    |extremal n k - extremal n l| ≤ 3 * |(k : ℝ) - l| := by
  rcases le_total k l with hkl | hlk
  · have h := extremal_edit_bounds n k l hkl hl
    have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
    rw [abs_of_nonpos (sub_nonpos.mpr hcast), abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := extremal_edit_bounds n l k hlk hk
    have hcast : (l : ℝ) ≤ k := by exact_mod_cast hlk
    rw [abs_of_nonneg (sub_nonneg.mpr hcast), abs_le]
    constructor <;> linarith [h.1, h.2]

theorem edge_count_le_choose (G : SimpleGraph (Fin n)) : G.edgeSet.ncard ≤ n.choose 2 := by
  classical
  rw [← finiteEdges_card]
  simpa only [finiteEdges, Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two

theorem value_le_extremal_edit (G : SimpleGraph (Fin n)) (k : ℕ) (hk : k ≤ n.choose 2) :
    value G ≤ extremal n k + 3 * |(G.edgeSet.ncard : ℝ) - k| := by
  have h := extremal_abs_sub_le n G.edgeSet.ncard k (edge_count_le_choose G) hk
  have hmax := value_le_extremal G
  have hle := (abs_le.mp h).2
  linarith

end Erdos1017.FractionalGraph
