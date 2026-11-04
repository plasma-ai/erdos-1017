module

public import Erdos1017.FractionalLimit.FractionalGraph
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Tactic.Linarith

/-!
# Subset weights and adding one edge to a fractional graph

This module defines the pair load `pairLoad` of weights on finite vertex subsets
and the subset-feasibility notion that allows transfers between graphs, and
proves that adding an absent edge raises the fractional optimum by at most one
(`value_add_edge_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators

variable {n : ℕ}

theorem moment_apply (G : SimpleGraph (Fin n)) (w : Clique G → ℝ) (e : Edge G) :
    FinitePrimal.moment (column G) w e = ∑ K, w K * column G K e := by
  let ev : (Edge G → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj e
  change ev (∑ K, w K • column G K) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro K _
  exact map_smul ev (w K) (column G K)

/-- The edge load of weights indexed by all finite vertex subsets. -/
def pairLoad (w : Finset (Fin n) → ℝ) (u v : Fin n) : ℝ :=
  ∑ S, if u ∈ S ∧ v ∈ S then w S else 0

/-- Extending clique weights by zero permits transfers between different graphs. -/
def SubsetFeasible (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧
    (∀ S, w S ≠ 0 → 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧
    ∀ u v, G.Adj u v → pairLoad w u v = 1

theorem sum_clique_subsets (G : SimpleGraph (Fin n)) (f : Finset (Fin n) → ℝ)
    (hf : ∀ S : Finset (Fin n), ¬(2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) → f S = 0) :
    (∑ K : Clique G, f K.val) = ∑ S, f S := by
  classical
  let e : Clique G ≃ {S : Finset (Fin n) // 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))} :=
    { toFun K := ⟨K.val, K.property⟩
      invFun K := ⟨K.val, K.property⟩
      left_inv K := by cases K; rfl
      right_inv K := by cases K; rfl }
  rw [Fintype.sum_equiv e (fun K => f K.val) (fun K => f K.val) (fun _ => rfl)]
  rw [← Finset.sum_subtype (Finset.univ.filter fun S : Finset (Fin n) =>
    2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) (by simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))
  · simp [hS]
  · simp [hS, hf S hS]

def extendWeights (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (S : Finset (Fin n)) : ℝ := by
  classical
  exact if hS : 2 ≤ S.card ∧ G.IsClique (S : Set (Fin n)) then w ⟨S, hS⟩ else 0

theorem extendWeights_sum (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (f : Finset (Fin n) → ℝ) :
    (∑ S, extendWeights G w S * f S) = ∑ K : Clique G, w K * f K.val := by
  rw [← sum_clique_subsets G (fun S => extendWeights G w S * f S)
    (by intro S hS; simp [extendWeights, hS])]
  apply Finset.sum_congr rfl
  intro K _
  have hK : (⟨K.val, K.property⟩ : Clique G) = K := by cases K; rfl
  simp only [extendWeights, dite_eq_left K.property, hK]

theorem extendWeights_feasible (G : SimpleGraph (Fin n)) (w : Clique G → ℝ)
    (hw : Feasible G w) : SubsetFeasible G (extendWeights G w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    unfold extendWeights
    split_ifs
    · exact hw.1 _
    · exact le_rfl
  · intro S hS
    by_contra hnot
    exact hS (by simp [extendWeights, hnot])
  · intro u v huv
    have h := congrFun hw.2 (⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr huv⟩ : Edge G)
    have h' := (moment_apply G w ⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr huv⟩).symm.trans h
    unfold pairLoad
    have heq : (∑ S : Finset (Fin n), if u ∈ S ∧ v ∈ S then extendWeights G w S else 0) =
        ∑ S : Finset (Fin n), extendWeights G w S * (if u ∈ S ∧ v ∈ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> simp
    rw [heq, extendWeights_sum]
    simpa [column, Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff] using h'

theorem subset_feasible_restrict (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) : Feasible G (fun K => w K.val) := by
  refine ⟨fun K => hw.1 K.val, ?_⟩
  funext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h u v =>
    have huv := (SimpleGraph.mem_edgeSet G).mp he
    apply (moment_apply G (fun K => w K.val) ⟨s(u, v), he⟩).trans
    simp only [column,
      Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [sum_clique_subsets G (fun S => w S * (if u ∈ S ∧ v ∈ S then 1 else 0))]
    · simpa [pairLoad, mul_ite] using hw.2.2 u v huv
    · intro S hS
      have hz : w S = 0 := by by_contra h; exact hS (hw.2.1 S h)
      simp [hz]

theorem subset_feasible_cost (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) : FinitePrimal.cost (fun K : Clique G => w K.val) = ∑ S, w S := by
  apply sum_clique_subsets
  intro S hS
  by_contra h
  exact hS (hw.2.1 S h)

theorem value_le_subset_cost (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) : value G ≤ ∑ S, w S := by
  obtain ⟨v, hv, hmin⟩ := exists_optimal G
  rw [value_eq_optimal G v hv hmin, ← subset_feasible_cost G w hw]
  exact hmin _ (subset_feasible_restrict G w hw)

/-- A nonedge cannot carry load from a measure supported on actual cliques. -/
theorem pairLoad_of_nonadjacent (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) (u v : Fin n) (hne : u ≠ v) (hno : ¬G.Adj u v) :
    pairLoad w u v = 0 := by
  apply Finset.sum_eq_zero
  intro S _
  split_ifs with hS
  · by_contra h
    exact hno ((hw.2.1 S h).2 hS.1 hS.2 hne)
  · rfl

theorem pairLoad_add (w z : Finset (Fin n) → ℝ) (u v : Fin n) :
    pairLoad (fun S => w S + z S) u v = pairLoad w u v + pairLoad z u v := by
  unfold pairLoad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem pairLoad_single (S : Finset (Fin n)) (a : ℝ) (u v : Fin n) :
    pairLoad (fun T => if T = S then a else 0) u v = if u ∈ S ∧ v ∈ S then a else 0 := by
  unfold pairLoad
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    simp [hT]
  · simp

/-- Add the new edge itself, with unit weight, to an old fractional partition. -/
def addEdgeWeights (w : Finset (Fin n) → ℝ) (u v : Fin n) (S : Finset (Fin n)) : ℝ :=
  w S + if S = {u, v} then 1 else 0

theorem addEdgeWeights_cost (w : Finset (Fin n) → ℝ) (u v : Fin n) :
    (∑ S, addEdgeWeights w u v S) = (∑ S, w S) + 1 := by
  simp [addEdgeWeights, Finset.sum_add_distrib]

theorem addEdgeWeights_feasible (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G w) (u v : Fin n) (hne : u ≠ v) (hno : ¬G.Adj u v) :
    SubsetFeasible (G ⊔ SimpleGraph.edge u v) (addEdgeWeights w u v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    unfold addEdgeWeights
    apply add_nonneg (hw.1 S)
    split_ifs <;> norm_num
  · intro S hS
    by_cases hpair : S = {u, v}
    · subst S
      refine ⟨by simp [Finset.card_pair hne], ?_⟩
      rw [Finset.coe_pair]
      apply SimpleGraph.isClique_pair.mpr
      intro _
      exact Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
    · have hweight : w S ≠ 0 := by simpa [addEdgeWeights, hpair] using hS
      exact ⟨(hw.2.1 S hweight).1, SimpleGraph.IsClique.mono le_sup_left (hw.2.1 S hweight).2⟩
  · intro a b hab
    change pairLoad (fun S => w S + if S = {u, v} then 1 else 0) a b = 1
    rw [pairLoad_add, pairLoad_single]
    rcases hab with hab | hab
    · have hpair : ¬(a ∈ ({u, v} : Finset (Fin n)) ∧ b ∈ ({u, v} : Finset (Fin n))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro ⟨ha | ha, hb | hb⟩
        · subst a; subst b; exact G.irrefl hab
        · subst a; subst b; exact hno hab
        · subst a; subst b; exact hno hab.symm
        · subst a; subst b; exact G.irrefl hab
      rw [hw.2.2 a b hab, ite_eq_right hpair]
      ring
    · obtain ⟨hab | hab, _⟩ := (SimpleGraph.edge_adj _ _ _ _).mp hab
      · rcases hab with ⟨rfl, rfl⟩
        rw [pairLoad_of_nonadjacent G w hw _ _ hne hno]
        simp
      · rcases hab with ⟨rfl, rfl⟩
        rw [pairLoad_of_nonadjacent G w hw _ _ hne.symm (fun h => hno h.symm)]
        simp

/-- Adding an absent edge raises the actual fractional graph optimum by at most one. -/
theorem value_add_edge_le (G : SimpleGraph (Fin n)) (u v : Fin n)
    (hne : u ≠ v) (hno : ¬G.Adj u v) :
    value (G ⊔ SimpleGraph.edge u v) ≤ value G + 1 := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  have hnew := addEdgeWeights_feasible G (extendWeights G w)
    (extendWeights_feasible G w hw) u v hne hno
  have hbound := value_le_subset_cost _ _ hnew
  rw [addEdgeWeights_cost] at hbound
  have hcost : (∑ S, extendWeights G w S) = FinitePrimal.cost w := by
    simpa [FinitePrimal.cost] using extendWeights_sum G w (fun _ => 1)
  rw [hcost, ← value_eq_optimal G w hw hmin] at hbound
  exact hbound

end Erdos1017.FractionalGraph
