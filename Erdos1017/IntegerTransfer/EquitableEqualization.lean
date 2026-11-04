module

public import Erdos1017.IntegerTransfer.FixedDensityCleaning
public import Erdos1017.IntegerTransfer.GraphEmbeddingRegularity
public import Erdos1017.IntegerTransfer.InducedEdgeLoss
public import Mathlib.Data.Fintype.EquivFin

/-!
# Equalizing the parts of a cleaned graph

An equitable partition contains equally sized labeled parts embedded in the
original parts, discarding fewer vertices than parts; the equalized cleaned
graph has pairs that are empty or square-root regular with the density floor,
and the edge loss is the regularity budget plus one vertex count per part
(`equalized_edge_loss`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.RegularityCleaning

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- An equitable partition contains equally sized labelled parts, with the
labels embedded into their original partition parts. -/
theorem exists_equal_parts_embedding (P : Finpartition (univ : Finset V))
    (hP : P.IsEquipartition) :
    ∃ e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V,
      ∀ i j, e (i, j) ∈ (P.parts.equivFin.symm i).val := by
  let a := P.parts.equivFin.symm
  have hcard (i : Fin P.parts.card) :
      Fintype.card (Fin (Fintype.card V / P.parts.card)) ≤
        Fintype.card (a i).val := by
    simpa only [Fintype.card_fin, Fintype.card_coe, card_univ] using
      hP.average_le_card_part (a i).property
  let b (i : Fin P.parts.card) : Fin (Fintype.card V / P.parts.card) ↪ (a i).val :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hcard i))
  refine ⟨⟨fun v => (b v.1 v.2).val, ?_⟩, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    change (b i x).val = (b j y).val at h
    have hij : i = j := by
      apply a.injective
      apply Subtype.ext
      exact P.eq_of_mem_parts (a i).property (a j).property
        (b i x).property (h.symm ▸ (b j y).property)
    subst j
    exact Prod.ext rfl ((b i).injective (Subtype.ext h))
  · intro i j
    exact (b i j).property

/-- The equalization discards fewer vertices than there are partition parts. -/
theorem equal_parts_remainder [Nonempty V] (P : Finpartition (univ : Finset V)) :
    0 < P.parts.card ∧ 0 < Fintype.card V / P.parts.card ∧
      Fintype.card V - P.parts.card * (Fintype.card V / P.parts.card) < P.parts.card := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨s, hs, _⟩ := P.exists_mem (mem_univ v)
  have hq : 0 < P.parts.card := Finset.card_pos.mpr ⟨s, hs⟩
  have hqn : P.parts.card ≤ Fintype.card V := by
    simpa only [card_univ] using P.card_parts_le_card
  have hN : 0 < Fintype.card V / P.parts.card := Nat.div_pos hqn hq
  have hmod := Nat.mod_lt (Fintype.card V) hq
  have hdiv := Nat.mod_add_div (Fintype.card V) P.parts.card
  exact ⟨hq, hN, by omega⟩

/-- Each equalized part retains at least half of its original part. -/
theorem equal_parts_half [Nonempty V] (P : Finpartition (univ : Finset V))
    (hP : P.IsEquipartition) {s : Finset V} (hs : s ∈ P.parts) :
    (s.card : ℝ) / 2 ≤ ((Fintype.card V / P.parts.card : ℕ) : ℝ) := by
  have hN := (equal_parts_remainder P).2.1
  have hcard := hP.card_part_le_average_add_one hs
  simp only [card_univ] at hcard
  have htwice : s.card ≤ 2 * (Fintype.card V / P.parts.card) := by omega
  have hcast : (s.card : ℝ) ≤ 2 * ((Fintype.card V / P.parts.card : ℕ) : ℝ) := by
    exact_mod_cast htwice
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)

/-- The labelled equal parts map into their original partition parts. -/
theorem mapped_equal_part_subset (P : Finpartition (univ : Finset V))
    (e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V)
    (he : ∀ i j, e (i, j) ∈ (P.parts.equivFin.symm i).val) (i : Fin P.parts.card) :
    (MultipartiteCounting.part i).map e ⊆ (P.parts.equivFin.symm i).val := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
  exact he i j

/-- The actual omitted vertex set is smaller than the partition. -/
theorem omitted_vertices_card [Nonempty V] (P : Finpartition (univ : Finset V))
    (e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V) :
    (univ \ univ.map e).card < P.parts.card := by
  simpa only [card_sdiff_of_subset (subset_univ _), card_univ, card_map,
    Fintype.card_prod, Fintype.card_fin] using (equal_parts_remainder P).2.2

/-- Equalized partition parts remain independent in the actual cleaned graph. -/
theorem equalized_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V))
    (e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V)
    (he : ∀ i j, e (i, j) ∈ (P.parts.equivFin.symm i).val)
    (η d : ℝ) (i : Fin P.parts.card) (a b : Fin (Fintype.card V / P.parts.card)) :
    ¬((G.regularityReduced P η d).comap e).Adj (i, a) (i, b) :=
  reduced_independent G P η d (P.parts.equivFin.symm i).property
    (e (i, a)) (he i a) (e (i, b)) (he i b)

/-- Mapping the equalized graph back into the original vertex set gives a subgraph. -/
theorem equalized_map_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V))
    (e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V) (η d : ℝ) :
    ((G.regularityReduced P η d).comap e).map e ≤ G :=
  (SimpleGraph.map_comap_le e _).trans SimpleGraph.regularityReduced_le

/-- Equalizing the cleaned graph gives actual labelled pairs which are empty,
or square-root regular and retain the fixed density floor minus the error. -/
theorem equalized_pair [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition)
    (e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V)
    (he : ∀ i j, e (i, j) ∈ (P.parts.equivFin.symm i).val)
    {η d : ℝ} (hη : η ≤ 1 / 4) (i j : Fin P.parts.card) :
    (∀ x ∈ MultipartiteCounting.part i, ∀ y ∈ MultipartiteCounting.part j,
      ¬((G.regularityReduced P η d).comap e).Adj x y) ∨
      (((G.regularityReduced P η d).comap e).IsUniform (Real.sqrt η)
          (MultipartiteCounting.part i) (MultipartiteCounting.part j) ∧
        d - η ≤ ((G.regularityReduced P η d).comap e).edgeDensity
          (MultipartiteCounting.part i) (MultipartiteCounting.part j)) := by
  have hroot : Real.sqrt η ≤ 1 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hsize (k : Fin P.parts.card) :
      (((P.parts.equivFin.symm k).val.card : ℝ) * Real.sqrt η) ≤
        ((MultipartiteCounting.part k).map e).card := by
    calc
      _ ≤ (P.parts.equivFin.symm k).val.card * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg _)
      _ = ((P.parts.equivFin.symm k).val.card : ℝ) / 2 := by ring
      _ ≤ ((Fintype.card V / P.parts.card : ℕ) : ℝ) :=
        equal_parts_half P hP (P.parts.equivFin.symm k).property
      _ = _ := by simp only [Finset.card_map, MultipartiteCounting.part, Finset.card_univ,
          Fintype.card_fin]
  obtain hempty | ⟨hreg, hden⟩ := trimmed_reduced_pair G P hη
    (P.parts.equivFin.symm i).property (P.parts.equivFin.symm j).property
    (mapped_equal_part_subset P e he i) (mapped_equal_part_subset P e he j)
    (hsize i) (hsize j)
  · refine Or.inl ?_
    intro x hx y hy hxy
    exact hempty (e x) (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      (e y) (Finset.mem_map.mpr ⟨y, hy, rfl⟩) hxy
  · refine Or.inr ⟨GraphEmbedding.isUniform_comap _ e _ _ _ hreg, ?_⟩
    rw [GraphEmbedding.edgeDensity_comap]
    exact hden

/-- Cleaning and equalizing lose the regularity deletion budget plus at most
one ambient vertex-count of edges for each original partition part. -/
theorem equalized_edge_loss [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition)
    (e : (Fin P.parts.card × Fin (Fintype.card V / P.parts.card)) ↪ V)
    {η d τ : ℝ} (hη : 0 < η) (hd : 0 < d) (hτ : 0 < τ)
    (hPreg : P.IsUniform G η) (hparts : 4 / τ ≤ (P.parts.card : ℝ)) :
    (G.edgeFinset.card : ℝ) - (((G.regularityReduced P η d).comap e).map e).edgeFinset.card <
      (2 * η + 2 * d + τ / 4) * (Fintype.card V : ℝ) ^ 2 +
        P.parts.card * (Fintype.card V : ℝ) := by
  have hclean := reduced_edge_loss G P hη hd hτ hP hPreg hparts
  have htrim := GraphEmbedding.induced_edge_loss (G.regularityReduced P η d) e
  have hD : ((univ \ univ.map e).card : ℝ) < P.parts.card := by
    exact_mod_cast omitted_vertices_card P e
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hsmall := mul_lt_mul_of_pos_right hD hn
  linarith

end Erdos1017.RegularityCleaning
