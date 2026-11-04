module

public import Erdos1017.Models.FractionalBoundedDual
public import Erdos1017.FractionalLimit.FractionalGraphCounts
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
# Cloning whole classes under an optimal dual

For a graph that is not complete multipartite, an optimal signed dual yields a
nondecreasing whole-class clone with strictly fewer distinct open-neighborhood
rows (`neighborhoodRowCount`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FractionalGraph

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- The number of distinct actual open-neighborhood rows. -/
def neighborhoodRowCount (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.image G.neighborSet).card

private def cloneClassMap (G : SimpleGraph (Fin n)) (b a : Fin n) (x : Fin n) : Fin n :=
  if G.neighborSet x = G.neighborSet b then a else x

private theorem clone_row_count_lt (G : SimpleGraph (Fin n)) (b a : Fin n)
    (hab : G.neighborSet a ≠ G.neighborSet b) :
    neighborhoodRowCount (G.comap (cloneClassMap G b a)) < neighborhoodRowCount G := by
  classical
  let π := cloneClassMap G b a
  let rows := Finset.univ.image G.neighborSet
  have hπ (x : Fin n) : G.neighborSet (π x) ≠ G.neighborSet b := by
    by_cases hx : G.neighborSet x = G.neighborSet b
    · simpa only [π, cloneClassMap, hx, ite_true] using hab
    · change G.neighborSet (if G.neighborSet x = G.neighborSet b then a else x) ≠ _
      rw [ite_eq_right hx]
      exact hx
  have hsub : Finset.univ.image (G.comap π).neighborSet ⊆
      (rows.erase (G.neighborSet b)).image (Set.preimage π) := by
    intro s hs
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
    apply Finset.mem_image.mpr
    refine ⟨G.neighborSet (π x), Finset.mem_erase.mpr ⟨hπ x, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨π x, Finset.mem_univ _, rfl⟩
    · rfl
  have hb : G.neighborSet b ∈ rows := Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  exact (Finset.card_le_card hsub).trans_lt
    ((Finset.card_image_le).trans_lt (Finset.card_erase_lt_of_mem hb))

private theorem row_eq_nonadj (G : SimpleGraph (Fin n)) {x b : Fin n}
    (hx : G.neighborSet x = G.neighborSet b) : ¬G.Adj x b := by
  intro h
  have hb : b ∈ G.neighborSet b := hx ▸ h
  exact G.irrefl hb

private theorem row_eq_adj_iff (G : SimpleGraph (Fin n)) {x b a : Fin n}
    (hx : G.neighborSet x = G.neighborSet b) : G.Adj x a ↔ G.Adj b a := by
  change a ∈ G.neighborSet x ↔ a ∈ G.neighborSet b
  rw [hx]

private theorem clone_sum_identity (G : SimpleGraph (Fin n)) (b a : Fin n)
    (hab : ¬G.Adj a b) (z : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, z i j = z j i) (hzero : ∀ i j, ¬G.Adj i j → z i j = 0) :
    (∑ i, ∑ j, z (cloneClassMap G b a i) (cloneClassMap G b a j)) =
      (∑ i, ∑ j, z i j) +
        2 * ∑ i, if G.neighborSet i = G.neighborSet b then
          (∑ j, z a j) - (∑ j, z i j) else 0 := by
  classical
  let B := fun x => G.neighborSet x = G.neighborSet b
  have hBzero (i j : Fin n) (hi : B i) (hj : B j) : z i j = 0 := by
    apply hzero
    intro hij
    have hbj : G.Adj b j := (row_eq_adj_iff G hi).mp hij
    exact row_eq_nonadj G hj (G.adj_symm hbj)
  have haB (j : Fin n) (hj : B j) : z a j = 0 := by
    apply hzero
    intro haj
    exact hab (G.adj_symm ((row_eq_adj_iff G hj).mp (G.adj_symm haj)))
  have hterm (i j : Fin n) :
      z (cloneClassMap G b a i) (cloneClassMap G b a j) = z i j +
        (if B i then z a j - z i j else 0) +
        (if B j then z i a - z i j else 0) := by
    by_cases hi : B i <;> by_cases hj : B j
    · have hia : z i a = 0 := (hsym i a).trans (haB i hi)
      simp only [cloneClassMap, show G.neighborSet i = G.neighborSet b from hi, hi,
        show G.neighborSet j = G.neighborSet b from hj, hj, ite_true,
        hzero a a G.irrefl, hBzero i j hi hj, haB j hj, hia, sub_self, add_zero]
    · simp only [cloneClassMap, show G.neighborSet i = G.neighborSet b from hi, hi,
        show ¬G.neighborSet j = G.neighborSet b from hj, hj, ite_true, ite_false]
      ring
    · simp only [cloneClassMap, show ¬G.neighborSet i = G.neighborSet b from hi, hi,
        show G.neighborSet j = G.neighborSet b from hj, hj, ite_false, ite_true]
      ring
    · simp only [cloneClassMap, show ¬G.neighborSet i = G.neighborSet b from hi, hi,
        show ¬G.neighborSet j = G.neighborSet b from hj, hj, ite_false, add_zero]
  have hleft : (∑ i, ∑ j, if B i then z a j - z i j else 0) =
      ∑ i, if B i then (∑ j, z a j) - (∑ j, z i j) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : B i <;> simp only [hi, ite_true, ite_false, Finset.sum_const_zero,
      Finset.sum_sub_distrib]
  have hright : (∑ i, ∑ j, if B j then z i a - z i j else 0) =
      ∑ i, if B i then (∑ j, z a j) - (∑ j, z i j) else 0 := by
    rw [Finset.sum_comm]
    have heq (i j : Fin n) : z j a - z j i = z a j - z i j := by
      rw [hsym j a, hsym j i]
    simp_rw [heq]
    exact hleft
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [hleft, hright]
  ring

private theorem support_objective_eq (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) :
    WeightedGraph.objective (fun _ => 1) y + (G.edgeSet.ncard : ℝ) =
      (∑ i, ∑ j, (y i j + (if G.Adj i j then 1 else 0))) / 2 := by
  classical
  have hcount : (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) =
      2 * (G.edgeSet.ncard : ℝ) := by exact_mod_cast ordered_edge_count G
  simp only [WeightedGraph.objective, mul_one, Finset.sum_add_distrib]
  rw [hcount]
  ring

private theorem clone_support_ge (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hopt : WeightedGraph.objective (fun _ => 1) y = value G)
    (b a : Fin n) (hab : ¬G.Adj a b)
    (hprice : ∀ i, G.neighborSet i = G.neighborSet b →
      (∑ j, (y i j + (if G.Adj i j then 1 else 0))) ≤
        ∑ j, (y a j + (if G.Adj a j then 1 else 0))) :
    value G + (G.edgeSet.ncard : ℝ) ≤
      value (G.comap (cloneClassMap G b a)) +
        ((G.comap (cloneClassMap G b a)).edgeSet.ncard : ℝ) := by
  classical
  let z := fun i j => y i j + (if G.Adj i j then (1 : ℝ) else 0)
  let π := cloneClassMap G b a
  have hsym (i j : Fin n) : z i j = z j i := by
    dsimp [z]
    rw [hy.1 i j, G.adj_comm]
  have hzero (i j : Fin n) (hij : ¬G.Adj i j) : z i j = 0 := by
    simp only [z, hy.2.1 i j hij, hij, ite_false, add_zero]
  have hgain : 0 ≤ ∑ i, if G.neighborSet i = G.neighborSet b then
      (∑ j, z a j) - (∑ j, z i j) else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs with hi
    · exact sub_nonneg.mpr (hprice i hi)
    · exact le_rfl
  have hsum := clone_sum_identity G b a hab z hsym hzero
  have hweak := WeightedGraph.dual_objective_le_value (G.comap π)
    (fun i j => y (π i) (π j)) (WeightedGraph.dualFeasible_comap G π y hy)
  have hold := support_objective_eq G y
  have hnew := support_objective_eq (G.comap π) (fun i j => y (π i) (π j))
  rw [hopt] at hold
  change WeightedGraph.objective (fun _ => 1) (fun i j => y (π i) (π j)) +
    ((G.comap π).edgeSet.ncard : ℝ) = (∑ i, ∑ j, z (π i) (π j)) / 2 at hnew
  change value G + (G.edgeSet.ncard : ℝ) = (∑ i, ∑ j, z i j) / 2 at hold
  change (∑ i, ∑ j, z (π i) (π j)) = _ at hsum
  linarith

/-- A genuine optimal signed dual supplies a nondecreasing whole-class
clone whenever the original graph is not complete multipartite. The new
graph has strictly fewer actual open-neighborhood rows. -/
theorem exists_support_clone (G : SimpleGraph (Fin n))
    (y : Fin n → Fin n → ℝ) (hy : WeightedGraph.DualFeasible G y)
    (hopt : WeightedGraph.objective (fun _ => 1) y = value G)
    (hnot : ¬G.IsCompleteMultipartite) :
    ∃ H : SimpleGraph (Fin n),
      value G + (G.edgeSet.ncard : ℝ) ≤ value H + (H.edgeSet.ncard : ℝ) ∧
        neighborhoodRowCount H < neighborhoodRowCount G := by
  classical
  have hbad : ∃ b a, ¬G.Adj a b ∧ G.neighborSet a ≠ G.neighborSet b := by
    by_contra h
    push Not at h
    apply hnot
    refine ⟨?_⟩
    intro x v z hxv hvz hxz
    have heq := h v x hxv
    apply hvz
    change z ∈ G.neighborSet v
    rw [← heq]
    exact hxz
  obtain ⟨b, a, hab, hrows⟩ := hbad
  let price := fun i => ∑ j, (y i j + (if G.Adj i j then (1 : ℝ) else 0))
  let C := Finset.univ.filter fun i =>
    G.neighborSet i = G.neighborSet a ∨ G.neighborSet i = G.neighborSet b
  have haC : a ∈ C := by simp [C]
  obtain ⟨v, hv, hmax⟩ := C.exists_max_image price ⟨a, haC⟩
  have hvclass := (Finset.mem_filter.mp hv).2
  rcases hvclass with hva | hvb
  · have hvb : G.neighborSet v ≠ G.neighborSet b := fun h => hrows (hva.symm.trans h)
    refine ⟨G.comap (cloneClassMap G b v), ?_, clone_row_count_lt G b v hvb⟩
    apply clone_support_ge G y hy hopt b v
    · exact fun h => hab ((row_eq_adj_iff G hva).mp h)
    · intro i hi
      apply hmax i
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr hi
  · have hva : G.neighborSet v ≠ G.neighborSet a := fun h => hrows (h.symm.trans hvb)
    refine ⟨G.comap (cloneClassMap G a v), ?_, clone_row_count_lt G a v hva⟩
    apply clone_support_ge G y hy hopt a v
    · intro h
      exact hab (G.adj_symm ((row_eq_adj_iff G hvb).mp h))
    · intro i hi
      apply hmax i
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl hi

end Erdos1017.FractionalGraph
