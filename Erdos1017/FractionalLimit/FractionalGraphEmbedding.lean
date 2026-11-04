module

public import Erdos1017.FractionalLimit.FractionalGraphDelete
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Fractional value under vertex embeddings

This module transports fractional partition weights along a vertex embedding in
both directions, so that relabeling vertices and adding any number of isolated
vertices preserves the value (`value_map`) and the edge count
(`edge_count_map`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n m : ℕ}

def embeddedWeights (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m) (w : Clique G → ℝ) :
    Finset (Fin m) → ℝ := sampleWeights w (fun K => K.val.map f)

theorem embedded_clique (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m) (K : Clique G) :
    (G.map f).IsClique (K.val.map f : Set (Fin m)) := by
  intro u hu v hv huv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
  exact SimpleGraph.map_adj_apply.mpr (K.property.2 hi hj (fun h => huv (congrArg f h)))

theorem embeddedWeights_feasible (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m)
    (w : Clique G → ℝ) (hw : Feasible G w) : SubsetFeasible (G.map f) (embeddedWeights G f w) := by
  refine ⟨sampleWeights_nonneg _ _ hw.1,
    sampleWeights_supported _ _ _ (embedded_clique G f), ?_⟩
  intro u v huv
  obtain ⟨i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj f G u v).mp huv
  rw [embeddedWeights, sampleWeights_pairLoad _ _ _ _ huv.ne]
  simp only [Finset.mem_map']
  have hm := (moment_apply G w ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr hij⟩).symm.trans
    (congrFun hw.2 ⟨s(i, j), (SimpleGraph.mem_edgeSet G).mpr hij⟩)
  simpa [column, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff] using hm

theorem value_map_le (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m) :
    value (G.map f) ≤ value G := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  rw [value_eq_optimal G w hw hmin]
  exact (value_le_subset_cost _ _ (embeddedWeights_feasible G f w hw)).trans
    (sampleWeights_cost_le _ _ hw.1)

def restrictedSet (f : Fin n ↪ Fin m) (S : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i ∈ S

@[simp] theorem mem_restrictedSet (f : Fin n ↪ Fin m) (S : Finset (Fin m)) (i : Fin n) :
    i ∈ restrictedSet f S ↔ f i ∈ S := by simp [restrictedSet]

def restrictedWeights (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m)
    (w : Clique (G.map f) → ℝ) : Finset (Fin n) → ℝ :=
  sampleWeights w (fun K => restrictedSet f K.val)

theorem restricted_clique (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m)
    (K : Clique (G.map f)) : G.IsClique (restrictedSet f K.val : Set (Fin n)) := by
  intro i hi j hj hij
  exact SimpleGraph.map_adj_apply.mp (K.property.2
    ((mem_restrictedSet f K.val i).mp hi) ((mem_restrictedSet f K.val j).mp hj)
    (fun h => hij (f.injective h)))

theorem restrictedWeights_feasible (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m)
    (w : Clique (G.map f) → ℝ) (hw : Feasible (G.map f) w) :
    SubsetFeasible G (restrictedWeights G f w) := by
  refine ⟨sampleWeights_nonneg _ _ hw.1,
    sampleWeights_supported _ _ _ (restricted_clique G f), ?_⟩
  intro i j hij
  rw [restrictedWeights, sampleWeights_pairLoad _ _ _ _ hij.ne]
  simp only [mem_restrictedSet]
  have hab : (G.map f).Adj (f i) (f j) := SimpleGraph.map_adj_apply.mpr hij
  let e : Edge (G.map f) := ⟨s(f i, f j), (SimpleGraph.mem_edgeSet _).mpr hab⟩
  have hm := (moment_apply _ w e).symm.trans (congrFun hw.2 e)
  simpa [column, e, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff] using hm

/-- Relabeling vertices and adding any number of isolated vertices preserves the value. -/
theorem value_map (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m) : value (G.map f) = value G := by
  apply le_antisymm (value_map_le G f)
  obtain ⟨w, hw, hmin⟩ := exists_optimal (G.map f)
  rw [value_eq_optimal _ w hw hmin]
  exact (value_le_subset_cost _ _ (restrictedWeights_feasible G f w hw)).trans
    (sampleWeights_cost_le _ _ hw.1)

theorem edge_count_map (G : SimpleGraph (Fin n)) (f : Fin n ↪ Fin m) :
    (G.map f).edgeSet.ncard = G.edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ f.sym2Map.injective

end Erdos1017.FractionalGraph
