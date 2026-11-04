module

public import Erdos1017.SelectedModel.Capped.FractionalCappedGraph

/-!
# Bounded optimal duals of the capped clique LP

Deleting one edge raises the capped fractional optimum by at most three, so
every finite restricted clique LP has an attained optimal dual whose signed edge
charges lie in the compact capped color interval (`exists_bounded_dual`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FractionalCappedGraph

open FractionalGraph (Edge pairLoad)

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- Subset weights retain both actual clique support and the order cap. -/
def SubsetFeasible (G : SimpleGraph (Fin n)) (N : ℕ) (w : Finset (Fin n) → ℝ) : Prop :=
  FractionalGraph.SubsetFeasible G w ∧ ∀ S, w S ≠ 0 → S.card ≤ N

theorem sum_clique_subsets (G : SimpleGraph (Fin n)) (N : ℕ) (f : Finset (Fin n) → ℝ)
    (hf : ∀ S : Finset (Fin n), ¬((2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧ S.card ≤ N) → f S = 0) :
    (∑ K : Clique G N, f K.val.val) = ∑ S, f S := by
  let e : Clique G N ≃ {S : Finset (Fin n) //
      (2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧ S.card ≤ N} :=
    { toFun K := ⟨K.val.val, K.val.property, K.property⟩
      invFun S := ⟨⟨S.val, S.property.1⟩, S.property.2⟩
      left_inv K := by cases K; rfl
      right_inv S := by cases S; rfl }
  rw [Fintype.sum_equiv e (fun K => f K.val.val) (fun S => f S.val) (fun _ => rfl)]
  rw [← Finset.sum_subtype (Finset.univ.filter fun S : Finset (Fin n) =>
      (2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧ S.card ≤ N) (by simp) f,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : (2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧ S.card ≤ N
  · simp [hS]
  · simp [hS, hf S hS]

def extendWeights (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  if hS : (2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧ S.card ≤ N then
    w ⟨⟨S, hS.1⟩, hS.2⟩ else 0

theorem extendWeights_sum (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ)
    (f : Finset (Fin n) → ℝ) :
    (∑ S, extendWeights G N w S * f S) = ∑ K : Clique G N, w K * f K.val.val := by
  rw [← sum_clique_subsets G N (fun S => extendWeights G N w S * f S)
    (by intro S hS; simp [extendWeights, hS])]
  apply Finset.sum_congr rfl
  intro K _
  have hK : (⟨⟨K.val.val, K.val.property⟩, K.property⟩ : Clique G N) = K := by cases K; rfl
  have hprop : (2 ≤ K.val.val.card ∧ G.IsClique (K.val.val : Set (Fin n))) ∧ K.val.val.card ≤ N :=
    ⟨K.val.property, K.property⟩
  simp only [extendWeights, dite_eq_left hprop, hK]

theorem extendWeights_feasible (G : SimpleGraph (Fin n)) (N : ℕ) (w : Clique G N → ℝ)
    (hw : Feasible G N w) : SubsetFeasible G N (extendWeights G N w) := by
  have hsupport (S : Finset (Fin n)) (hS : extendWeights G N w S ≠ 0) :
      (2 ≤ S.card ∧ G.IsClique (S : Set (Fin n))) ∧ S.card ≤ N := by
    by_contra hnot
    exact hS (by simp [extendWeights, hnot])
  refine ⟨⟨?_, fun S hS => (hsupport S hS).1, ?_⟩, fun S hS => (hsupport S hS).2⟩
  · intro S
    unfold extendWeights
    split_ifs
    · exact hw.1 _
    · exact le_rfl
  · intro u v huv
    let e : Edge G := ⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr huv⟩
    have h := congrFun hw.2 e
    have h' := (moment_apply G N w e).symm.trans h
    unfold FractionalGraph.pairLoad
    have heq : (∑ S, if u ∈ S ∧ v ∈ S then extendWeights G N w S else 0) =
        ∑ S, extendWeights G N w S * (if u ∈ S ∧ v ∈ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> simp
    rw [heq, extendWeights_sum]
    simpa [column, FractionalGraph.column, e, Sym2.toFinset_mk_eq,
      Finset.insert_subset_iff, Finset.singleton_subset_iff] using h'

theorem subset_feasible_restrict (G : SimpleGraph (Fin n)) (N : ℕ) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G N w) : Feasible G N (fun K => w K.val.val) := by
  refine ⟨fun K => hw.1.1 K.val.val, ?_⟩
  funext e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h u v =>
    have huv := (SimpleGraph.mem_edgeSet G).mp he
    apply (moment_apply G N (fun K => w K.val.val) ⟨s(u, v), he⟩).trans
    simp only [column, FractionalGraph.column,
      Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [sum_clique_subsets G N (fun S => w S * (if u ∈ S ∧ v ∈ S then 1 else 0))]
    · simpa [FractionalGraph.pairLoad, mul_ite] using hw.1.2.2 u v huv
    · intro S hS
      have hz : w S = 0 := by
        by_contra h
        exact hS ⟨hw.1.2.1 S h, hw.2 S h⟩
      simp [hz]

theorem subset_feasible_cost (G : SimpleGraph (Fin n)) (N : ℕ) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G N w) : FinitePrimal.cost (fun K : Clique G N => w K.val.val) = ∑ S, w S := by
  apply sum_clique_subsets
  intro S hS
  by_contra h
  exact hS ⟨hw.1.2.1 S h, hw.2 S h⟩

theorem value_le_subset_cost (G : SimpleGraph (Fin n)) (N : ℕ) (w : Finset (Fin n) → ℝ)
    (hw : SubsetFeasible G N w) : value G N ≤ ∑ S, w S := by
  rw [← subset_feasible_cost G N w hw]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨v, hv, rfl⟩
    exact Finset.sum_nonneg (fun K _ => hv.1 K)
  · exact ⟨_, subset_feasible_restrict G N w hw, rfl⟩

/-- Every nonzero repair output is literally a subset of its parent. This
is the additional size control needed for the capped LP. -/
theorem repairKernel_subset (S : Finset (Fin n)) (u v : Fin n) (hu : u ∈ S) (hv : v ∈ S)
    (T : Finset (Fin n)) (hT : FractionalGraph.repairKernel S u v T ≠ 0) : T ⊆ S := by
  by_cases hcard : 2 ≤ T.card
  · unfold FractionalGraph.repairKernel FractionalGraph.sampleWeights at hT
    rw [ite_eq_left hcard] at hT
    obtain ⟨ω, _, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    split_ifs at hω with heq
    · simpa only [heq] using FractionalGraph.repairSelection_subset S u v hu hv ω.1 ω.2
    · exact (hω rfl).elim
  · exact (hT (by simp [FractionalGraph.repairKernel, FractionalGraph.sampleWeights, hcard])).elim

theorem deletionKernel_subset (S : Finset (Fin n)) (u v : Fin n)
    (T : Finset (Fin n)) (hT : FractionalGraph.deletionKernel S u v T ≠ 0) : T ⊆ S := by
  by_cases hcontains : u ∈ S ∧ v ∈ S
  · exact repairKernel_subset S u v hcontains.1 hcontains.2 T
      (by simpa only [FractionalGraph.deletionKernel, ite_eq_left hcontains] using hT)
  · have hTS : T = S := by
      by_contra h
      exact hT (by simp [FractionalGraph.deletionKernel, hcontains, h])
    exact hTS ▸ Finset.Subset.rfl

theorem deleteEdgeWeights_feasible (G : SimpleGraph (Fin n)) (N : ℕ)
    (w : Finset (Fin n) → ℝ) (hw : SubsetFeasible G N w) (u v : Fin n) (huv : u ≠ v) :
    SubsetFeasible (G.deleteEdges {s(u, v)}) N (FractionalGraph.deleteEdgeWeights w u v) := by
  refine ⟨FractionalGraph.deleteEdgeWeights_feasible G w hw.1 u v huv, ?_⟩
  intro T hT
  obtain ⟨S, _, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  have hparts := mul_ne_zero_iff.mp hS
  exact (Finset.card_le_card (deletionKernel_subset S u v T hparts.2)).trans (hw.2 S hparts.1)

/-- Actual cost-four repair remains inside the old order cap, so deleting
one edge raises the capped fractional optimum by at most three. -/
theorem value_delete_edge_le (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N)
    (u v : Fin n) (huv : G.Adj u v) :
    value (G.deleteEdges {s(u, v)}) N ≤ value G N + 3 := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G N hN
  have hext := extendWeights_feasible G N w hw
  have hnew := deleteEdgeWeights_feasible G N (extendWeights G N w) hext u v huv.ne
  have hbound := (value_le_subset_cost _ N _ hnew).trans
    (FractionalGraph.deleteEdgeWeights_cost (extendWeights G N w) hext.1.1 u v)
  rw [hext.1.2.2 u v huv] at hbound
  have hcost : (∑ S, extendWeights G N w S) = FinitePrimal.cost w := by
    simpa [FinitePrimal.cost] using extendWeights_sum G N w (fun _ => 1)
  rw [hcost, ← value_eq_optimal G N w hw hmin] at hbound
  simpa using hbound

end Erdos1017.FractionalCappedGraph

namespace Erdos1017.WeightedGraph

open scoped BigOperators

variable {n : ℕ}

attribute [local instance] Classical.propDecidable

/-- Capped signed duals compare every actual capped subset partition. -/
theorem capped_dual_objective_le_subset_cost (G : SimpleGraph (Fin n)) (N : ℕ)
    (y : Fin n → Fin n → ℝ) (hy : CappedDualFeasible G N y)
    (w : Finset (Fin n) → ℝ) (hw : FractionalCappedGraph.SubsetFeasible G N w) :
    objective (fun _ => 1) y ≤ ∑ S, w S := by
  have hcharge : objective (fun _ => 1) y = ∑ S, w S * charge y S := by
    rw [weighted_charge_identity]
    unfold objective
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.Adj i j
    · simp [hw.1.2.2 i j hij]
    · simp [hy.2.1 i j hij]
  rw [hcharge]
  apply Finset.sum_le_sum
  intro S _
  by_cases hz : w S = 0
  · simp [hz]
  · have hS := hw.1.2.1 S hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (hy.2.2 S (hw.2 S hz) hS.2) (hw.1.1 S)

theorem capped_dual_objective_le_value (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N)
    (y : Fin n → Fin n → ℝ) (hy : CappedDualFeasible G N y) :
    objective (fun _ => 1) y ≤ FractionalCappedGraph.value G N := by
  obtain ⟨w, hw, hmin⟩ := FractionalCappedGraph.exists_optimal G N hN
  rw [FractionalCappedGraph.value_eq_optimal G N w hw hmin]
  have h := capped_dual_objective_le_subset_cost G N y hy
    (FractionalCappedGraph.extendWeights G N w) (FractionalCappedGraph.extendWeights_feasible G N w hw)
  have hcost := FractionalCappedGraph.extendWeights_sum G N w (fun _ => 1)
  simp only [mul_one] at hcost
  simpa only [hcost, FinitePrimal.cost] using h

private theorem capped_isSelectedEdge_swap (u v i j : Fin n) :
    isSelectedEdge u v i j ↔ isSelectedEdge u v j i := by
  simp only [isSelectedEdge]
  tauto

/-- Erasing an existing edge gives a feasible dual for the graph with that
edge deleted. -/
theorem capped_dualFeasible_eraseEdge (G : SimpleGraph (Fin n)) (N : ℕ)
    (y : Fin n → Fin n → ℝ) (hy : CappedDualFeasible G N y) (u v : Fin n)
    (huv : G.Adj u v) :
    CappedDualFeasible (G.deleteEdges {s(u, v)}) N (eraseEdge y u v) := by
  classical
  have hnot_selected {i j : Fin n} (h : ¬isSelectedEdge u v i j)
      (hij : G.Adj i j) : (G.deleteEdges {s(u, v)}).Adj i j := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hij, ?_⟩
    intro heq
    exact h (by simpa [isSelectedEdge, Sym2.eq_iff] using heq)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases h : isSelectedEdge u v i j
    · have h' := (capped_isSelectedEdge_swap u v i j).mp h
      simp [eraseEdge, h, h']
    · have h' := (capped_isSelectedEdge_swap u v i j).mpr.mt h
      simp [eraseEdge, h, h', hy.1 i j]
  · intro i j hij
    by_cases h : isSelectedEdge u v i j
    · simp [eraseEdge, h]
    · have hG : ¬G.Adj i j := fun hadj => hij (hnot_selected h hadj)
      simp [eraseEdge, h, hy.2.1 i j hG]
  · intro S hSN hS
    have hG : G.IsClique (S : Set (Fin n)) := by
      intro i hi j hj hij
      exact (SimpleGraph.deleteEdges_adj.mp (hS hi hj hij)).1
    have hno : ¬(u ∈ S ∧ v ∈ S) := by
      intro h
      have hadj := hS h.1 h.2 huv.ne
      exact (SimpleGraph.deleteEdges_adj.mp hadj).2 (Set.mem_singleton_iff.mpr rfl)
    have hsame : ∀ i ∈ S, ∀ j ∈ S, eraseEdge y u v i j = y i j := by
      intro i hi j hj
      have h : ¬isSelectedEdge u v i j := by
        intro h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hno ⟨hi, hj⟩
        · exact hno ⟨hj, hi⟩
      simp [eraseEdge, h]
    calc
      charge (eraseEdge y u v) S = charge y S := by
        rw [charge_eq_sum, charge_eq_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hsame i hi j hj
      _ ≤ 1 := hy.2.2 S hSN hG

/-- A two-vertex clique bounds every present edge charge by one. -/
private theorem capped_dualFeasible_entry_le_one (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N)
    (y : Fin n → Fin n → ℝ) (hy : CappedDualFeasible G N y) (i j : Fin n) :
    y i j ≤ 1 := by
  by_cases hij : G.Adj i j
  · have hclique : G.IsClique (({i, j} : Finset (Fin n)) : Set (Fin n)) := by
      simpa using (SimpleGraph.isClique_pair).mpr (fun _ => hij)
    have h := hy.2.2 {i, j} (by simpa [Finset.card_pair hij.ne] using hN) hclique
    have hdiagᵢ : y i i = 0 := hy.2.1 i i (fun h => G.irrefl h)
    have hdiagⱼ : y j j = 0 := hy.2.1 j j (fun h => G.irrefl h)
    have hcharge : charge y {i, j} = y i j := by
      rw [charge_eq_sum]
      simp [Finset.sum_pair hij.ne, hdiagᵢ, hdiagⱼ, hy.1 j i]
    rwa [hcharge] at h
  · rw [hy.2.1 i j hij]
    norm_num

/-- The capped optimal dual itself lies in the color box. The lower
bound uses the actual capped cost-three deletion comparison, whose repair
cliques were proved to stay below the imposed order. -/
theorem optimal_capped_dual_mem_Icc (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N)
    (y : Fin n → Fin n → ℝ) (hy : CappedDualFeasible G N y)
    (hopt : objective (fun _ => 1) y = FractionalCappedGraph.value G N) (i j : Fin n) :
    y i j ∈ Set.Icc (-3 : ℝ) 1 := by
  constructor
  · by_cases hij : G.Adj i j
    · have hnew := capped_dualFeasible_eraseEdge G N y hy i j hij
      have hweak := capped_dual_objective_le_value (G.deleteEdges {s(i, j)}) N hN
        (eraseEdge y i j) hnew
      have hdelete := FractionalCappedGraph.value_delete_edge_le G N hN i j hij
      rw [objective_eraseEdge y hy.1 i j hij.ne, hopt] at hweak
      linarith
    · rw [hy.2.1 i j hij]
      norm_num
  · exact capped_dualFeasible_entry_le_one G N hN y hy i j

/-- Independent finite clones preserve the tested clique orders. Image
cliques have cardinality at most the original tested subset. -/
theorem capped_dualFeasible_comap {k : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (π : Fin k → Fin n)
    (y : Fin n → Fin n → ℝ) (hy : CappedDualFeasible G N y) :
    CappedDualFeasible (G.comap π) N (fun i j => y (π i) (π j)) := by
  refine ⟨fun i j => hy.1 _ _, fun i j hij => hy.2.1 _ _ hij, ?_⟩
  intro S hSN hS
  rw [charge_comap G π y S hS]
  exact hy.2.2 _ ((Finset.card_image_le).trans hSN) (image_clique_of_comap G π S hS)

end Erdos1017.WeightedGraph

namespace Erdos1017.FractionalCappedGraph

variable {n : ℕ}

/-- Every finite restricted clique LP has an actual attained optimal dual
whose signed edge charges lie in the compact capped color interval. -/
theorem exists_bounded_dual (G : SimpleGraph (Fin n)) (N : ℕ) (hN : 2 ≤ N) :
    ∃ y : Fin n → Fin n → ℝ,
      WeightedGraph.CappedDualFeasible G N y ∧
      (∀ i j, y i j ∈ Set.Icc (-3 : ℝ) 1) ∧
      WeightedGraph.objective (fun _ => 1) y = value G N := by
  obtain ⟨y, hy, hopt⟩ := exists_optimal_dual G N hN
  exact ⟨y, hy, fun i j => WeightedGraph.optimal_capped_dual_mem_Icc G N hN y hy hopt i j, hopt⟩

end Erdos1017.FractionalCappedGraph
