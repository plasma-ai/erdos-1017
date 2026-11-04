module

public import Erdos1017.LowerBound.FractionalLimitEndpoints

/-!
# Balanced bipartite graphs and densities up to one quarter

Every density through one quarter is attained by subgraphs of balanced bipartite
graphs (`densityLimit_eq_self`), using clique and edge-count facts for colorings
and balanced bipartite graphs.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FractionalGraph

open scoped BigOperators Topology
open Filter

variable {n : ℕ}

theorem clique_card_two_of_coloring (G : SimpleGraph (Fin n)) (f : Fin n → Fin 2)
    (hf : ∀ i j, G.Adj i j → f i ≠ f j) (K : Clique G) : K.val.card = 2 := by
  have hinj : Set.InjOn f (K.val : Set (Fin n)) := by
    intro i hi j hj heq
    by_contra hij
    exact hf i j (K.property.2 hi hj hij) heq
  have hcard := Finset.card_le_card (Finset.subset_univ (K.val.image f))
  rw [Finset.card_image_of_injOn hinj] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  exact le_antisymm hcard K.property.1

theorem column_sum_of_card_two (G : SimpleGraph (Fin n)) (K : Clique G)
    (hK : K.val.card = 2) : (∑ e : Edge G, column G K e) = 1 := by
  classical
  obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp hK
  have hu : u ∈ K.val := by simp [hpair]
  have hv : v ∈ K.val := by simp [hpair]
  let e : Edge G := ⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr (K.property.2 hu hv huv)⟩
  rw [Finset.sum_eq_single e]
  · simp [column, e, hpair, Sym2.toFinset_mk_eq]
  · intro z _ hze
    have hnot : ¬ z.val.toFinset ⊆ K.val := by
      intro hz
      apply hze
      apply Subtype.ext
      obtain ⟨z, hzG⟩ := z
      induction z using Sym2.ind with
      | h a b =>
        have hab := (SimpleGraph.mem_edgeSet G).mp hzG
        simp only [hpair, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with ⟨ha | ha, hb | hb⟩
        · subst a; subst b; exact (hab.ne rfl).elim
        · subst a; subst b; rfl
        · subst a; subst b; exact Sym2.eq_swap
        · subst a; subst b; exact (hab.ne rfl).elim
    simp [column, hnot]
  · simp

theorem value_eq_edge_count_of_coloring (G : SimpleGraph (Fin n)) (f : Fin n → Fin 2)
    (hf : ∀ i j, G.Adj i j → f i ≠ f j) : value G = G.edgeSet.ncard := by
  obtain ⟨w, hw, hmin⟩ := exists_optimal G
  rw [value_eq_optimal G w hw hmin]
  have hload (e : Edge G) : (∑ K, w K * column G K e) = 1 :=
    (moment_apply G w e).symm.trans (congrFun hw.2 e)
  have hsum := congrArg (fun f : Edge G → ℝ => ∑ e, f e) (funext hload)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.mul_sum, column_sum_of_card_two G _ (clique_card_two_of_coloring G f hf _),
    mul_one] at hsum
  have hcard : Fintype.card (Edge G) = G.edgeSet.ncard := by
    let : Fintype G.edgeSet := Fintype.ofFinite _
    let e : Edge G ≃ G.edgeSet :=
      { toFun e := ⟨e.val, e.property⟩
        invFun e := ⟨e.val, e.property⟩
        left_inv e := by cases e; rfl
        right_inv e := by cases e; rfl }
    exact (Fintype.card_congr e).trans (Set.fintypeCard_eq_ncard G.edgeSet)
  simpa only [FinitePrimal.cost, hcard] using hsum

theorem balanced_bipartite_edge_count (t : ℕ) :
    (blowup (⊤ : SimpleGraph (Fin 2)) t).edgeSet.ncard = t ^ 2 := by
  rw [edge_count_blowup]
  have htop : (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard = 1 := by
    rw [← finiteEdges_card, finiteEdges_top_card]
    norm_num
  simp only [htop, mul_one]

theorem extremal_even_sparse (t k : ℕ) (hk : k ≤ t ^ 2) : extremal (2 * t) k = k := by
  apply le_antisymm (extremal_le _ _)
  obtain ⟨G, hG, hcount⟩ := exists_subgraph_edge_count
    (blowup (⊤ : SimpleGraph (Fin 2)) t) k ((balanced_bipartite_edge_count t).symm ▸ hk)
  have hf : ∀ i j, G.Adj i j → (finProdFinEquiv.symm i).1 ≠ (finProdFinEquiv.symm j).1 := by
    intro i j hij
    exact hG hij
  have hvalue := value_eq_edge_count_of_coloring G (fun i => (finProdFinEquiv.symm i).1) hf
  have hmax := value_le_extremal G
  simpa only [hvalue, hcount] using hmax

/-- Every density through one quarter is attained by subgraphs of balanced bipartite graphs. -/
theorem densityLimit_eq_self (d : ℝ) (hd : d ∈ Set.Icc (0 : ℝ) (1 / 4)) : densityLimit d = d := by
  let k : ℕ → ℕ := fun t => ⌊d * (2 * t : ℕ) ^ 2⌋₊
  have hk (t : ℕ) : k t ≤ t ^ 2 := by
    apply Nat.floor_le_of_le
    have h := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg (2 * (t : ℝ)))
    push_cast
    nlinarith [h]
  have hadmissible (t : ℕ) : k t ≤ (2 * t).choose 2 := by
    have h := edge_count_le_choose (blowup (⊤ : SimpleGraph (Fin 2)) t)
    rw [balanced_bipartite_edge_count] at h
    exact (hk t).trans h
  have hv : Tendsto (fun t : ℕ => 2 * t) atTop atTop :=
    tendsto_atTop_mono (fun t => show t ≤ 2 * t by omega) tendsto_id
  have hdensity : Tendsto (fun t : ℕ => (k t : ℝ) / (2 * t : ℕ) ^ 2) atTop (𝓝 d) :=
    (tendsto_floor_density d hd.1).comp hv
  have hcost := tendsto_extremal_of_density_along (fun t => 2 * t) k hv hadmissible d hdensity
  simp only [extremal_even_sparse _ _ (hk _)] at hcost
  exact tendsto_nhds_unique hcost hdensity

end Erdos1017.FractionalGraph
