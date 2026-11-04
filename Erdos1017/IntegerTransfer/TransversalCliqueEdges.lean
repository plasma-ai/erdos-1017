module

public import Erdos1017.IntegerTransfer.ThinnedGraph
public import Mathlib.Data.Finset.Prod

/-!
# Clique hypergraph of transversal assignments

A transversal assignment has a labeled vertex set and graph edges given by
increasing-label coordinates; the complete assignments form a clique hypergraph
on graph-edge coordinates, uniform of rank `k.choose 2`, and fixing `s` role
values leaves `n^(k-s)` assignments.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- A transversal's actual labelled vertex set. -/
def vertices (X : Fin k → A) : Finset (Fin k × A) :=
  Finset.univ.image (fun i => (i, X i))

/-- Its graph edges, represented by increasing-label coordinates. -/
def edges (X : Fin k → A) : Finset (Coordinate k A) :=
  (MultipartiteExtension.completeEdges k).image (coordinate (t := k) (u := 0) X)

omit [Fintype A] in
theorem vertices_card (X : Fin k → A) : (vertices X).card = k := by
  rw [vertices, Finset.card_image_of_injective _ (by intro i j h; exact congrArg Prod.fst h)]
  simp

omit [Fintype A] [DecidableEq A] in
theorem completeEdges_card (k : ℕ) : (MultipartiteExtension.completeEdges k).card = k.choose 2 := by
  simpa only [MultipartiteExtension.completeEdges, Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
    Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k)))

omit [Fintype A] in
theorem edges_card (X : Fin k → A) : (edges X).card = k.choose 2 := by
  rw [edges, Finset.card_image_of_injective _ (coordinate_injective (t := k) (u := 0) X), completeEdges_card]

omit [Fintype A] in
/-- Membership fixes both endpoint values; no unordered-edge multiplicity remains. -/
theorem mem_edges_iff (X : Fin k → A) (v : Coordinate k A) :
    v ∈ edges X ↔ v.1.1 < v.2.1 ∧ X v.1.1 = v.1.2 ∧ X v.2.1 = v.2.2 := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    exact ⟨(Finset.mem_filter.mp he).2, rfl, rfl⟩
  · rintro ⟨hlt, hleft, hright⟩
    apply Finset.mem_image.mpr
    refine ⟨(v.1.1, v.2.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
    exact Prod.ext (Prod.ext rfl hleft) (Prod.ext rfl hright)

omit [Fintype A] in
/-- Two distinct transversal assignments give distinct simple hyperedges. -/
theorem edges_injective (hk : 2 ≤ k) : Function.Injective (edges (k := k) (A := A)) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  intro X Y h
  funext i
  obtain ⟨j, hj⟩ := exists_ne i
  rcases lt_or_gt_of_ne hj.symm with hij | hji
  · have hmem : ((i, X i), (j, X j)) ∈ edges X := (mem_edges_iff X _).mpr ⟨hij, rfl, rfl⟩
    rw [h] at hmem
    exact ((mem_edges_iff Y _).mp hmem).2.1.symm
  · have hmem : ((j, X j), (i, X i)) ∈ edges X := (mem_edges_iff X _).mpr ⟨hji, rfl, rfl⟩
    rw [h] at hmem
    exact ((mem_edges_iff Y _).mp hmem).2.2.symm

/-- The actual complete transversal assignments of a graph. -/
def assignments (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj] : Finset (Fin k → A) :=
  MultipartiteCounting.assignments G (MultipartiteExtension.completeEdges k)

/-- The concrete clique hypergraph, whose vertices are graph-edge coordinates. -/
def hypergraph (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj] :
    Finset (Finset (Coordinate k A)) := (assignments G).image edges

/-- Every realizing assignment gives an actual k-vertex clique. -/
theorem vertices_isClique (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (X : Fin k → A) (hX : X ∈ assignments G) : G.IsClique (vertices X : Set (Fin k × A)) := by
  intro v hv w hw hvw
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
  have hij : i ≠ j := fun h => hvw (by rw [h])
  have hreal := (Finset.mem_filter.mp hX).2
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hreal (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
  · exact (hreal (j, i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩)).symm

/-- The concrete clique hypergraph is uniform of rank k.choose 2. -/
theorem hypergraph_uniform (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (e : Finset (Coordinate k A)) (he : e ∈ hypergraph G) : e.card = k.choose 2 := by
  obtain ⟨X, _, rfl⟩ := Finset.mem_image.mp he
  exact edges_card X

/-- Assignments fixed on a role subset, with all other coordinates free. -/
def fixed (S : Finset (Fin k)) (X : Fin k → A) : Finset (Fin k → A) :=
  Fintype.piFinset (fun i => if i ∈ S then {X i} else Finset.univ)

omit [DecidableEq A] in
theorem mem_fixed (S : Finset (Fin k)) (X Y : Fin k → A) :
    Y ∈ fixed S X ↔ ∀ i ∈ S, Y i = X i := by
  simp only [fixed, Fintype.mem_piFinset]
  constructor
  · intro h i hi
    simpa only [ite_eq_left hi, Finset.mem_singleton] using h i
  · intro h i
    by_cases hi : i ∈ S <;> simp [hi, h]

omit [DecidableEq A] in
/-- Fixing s distinct role values leaves exactly n^(k−s) assignments. -/
theorem fixed_card (S : Finset (Fin k)) (X : Fin k → A) :
    (fixed S X).card = Fintype.card A ^ (k - S.card) := by
  rw [fixed, Fintype.card_piFinset]
  have hcard (i : Fin k) : (if i ∈ S then ({X i} : Finset A) else Finset.univ).card =
      if i ∈ S then 1 else Fintype.card A := by split_ifs <;> simp
  simp only [hcard]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have hset : Finset.univ.filter (fun i : Fin k => i ∉ S) = Finset.univ \ S := by ext i; simp
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

end Erdos1017.TransversalClique
